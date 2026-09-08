"""Itanium C++ ABI: vtable layout, RTTI parsing, typeinfo-name demangling.

Reference: https://itanium-cxx-abi.github.io/cxx-abi/abi.html#rtti
Vtable layout around the address point AP (ptr = pointer size):
  AP - (3+i)*ptr : vbase offset of the i-th virtual base (classes with
                   virtual bases only; the primary base's come first, then
                   the class's own in inheritance graph order, nearest first)
  AP - 2*ptr : offset-to-top (0 for the primary table, negative otherwise)
  AP - ptr   : pointer to the typeinfo object (0 when built with -fno-rtti)
typeinfo object:
  [vptr][name_ptr]                              __class_type_info: no bases
  [vptr][name_ptr][base_ti]                     __si_class_type_info: one base
  [vptr][name_ptr][flags:u32][count:u32][{base_ti, offset_flags:long}...]
      __vmi_class_type_info; offset_flags holds the in-object offset in
      bits 8.. and the virtual (bit 0) / public (bit 1) flags below.
"""
import re

from binaryninja.enums import SymbolType

from .abi import read_slots, sign
from .facts import BaseRef, VtableInfo
from .names import _skip_group, _skip_ident, demangle

MAX_SLOTS = 4096
MAX_BASES = 64
MAX_DEPTH = 16
MAX_OBJECT = 1 << 24

ALLOCATORS = {
    "_Znwm", "_Znam", "_Znwj", "_Znaj",
    "_ZnwmRKSt9nothrow_t", "_ZnamRKSt9nothrow_t",
    "_ZnwjRKSt9nothrow_t", "_ZnajRKSt9nothrow_t",
    "_ZnwmSt11align_val_t", "_ZnamSt11align_val_t",
    "malloc", "calloc", "_malloc",
}

DEALLOCATORS = {
    "_ZdlPv", "_ZdlPvm", "_ZdaPv", "_ZdaPvm", "_ZdlPvj", "_ZdaPvj",
    "_ZdlPvSt11align_val_t", "_ZdlPvmSt11align_val_t", "free", "_free",
}

_NAME_RE = re.compile(r"^\*?[A-Za-z0-9_$.]+$")


def demangle_typeinfo_name(mangled):
    """Fallback demangler for the typeinfo-name subset (no _Z prefix).

    Handles length-prefixed identifiers, nested N...E names, the St
    abbreviation, and keeps template argument lists raw. A leading '*'
    (local or anonymous-namespace type) is dropped. Returns None when the
    grammar does not parse.
    """
    if not mangled:
        return None
    mangled = mangled.lstrip("*")
    try:
        name, pos = _parse_entity(mangled, 0)
        if name is None or pos != len(mangled):
            return None
        return name
    except (ValueError, IndexError):
        return None


def _parse_entity(s, pos):
    if s.startswith("St", pos):
        rest, pos = _parse_entity(s, pos + 2) if pos + 2 < len(s) else (None, pos + 2)
        return ("std::" + rest if rest else "std"), pos
    if s[pos] == "N":
        parts = []
        pos += 1
        while pos < len(s) and s[pos] != "E":
            part, pos = _parse_entity(s, pos)
            if part is None:
                return None, pos
            parts.append(part)
        if pos >= len(s):
            return None, pos
        return "::".join(parts), pos + 1
    if s[pos].isdigit():
        m = re.match(r"\d+", s[pos:])
        n = int(m.group(0))
        pos += len(m.group(0))
        name = s[pos:pos + n]
        if len(name) != n:
            return None, pos
        pos += n
        if s.startswith("I", pos):
            end = s.find("E", pos)
            if end == -1:
                return None, pos
            name += "<" + s[pos + 1:end] + ">"
            pos = end + 1
        return name, pos
    return None, pos


_DEMANGLED_PREFIXES = ("typeinfo for ", "typeinfo_for_", "typeinfo name for ",
                       "typeinfo_name_for_")


def _bn_demangle(bv, mangled):
    try:
        result = demangle(bv, mangled, "gnu3")
    except Exception:
        return None
    if result is None:
        return None
    name = "::".join(str(n) for n in result[1])
    for prefix in _DEMANGLED_PREFIXES:
        if name.startswith(prefix):
            name = name[len(prefix):]
    if not name or name.startswith("_Z"):
        return None
    return name


def demangle_name(bv, raw):
    """Demangle with Binary Ninja's GNU3 demangler, falling back to ours.

    The typeinfo name is a bare <type>; prefixing _Z makes it the encoding of
    a data object of that name, which demangles to the plain qualified name.
    """
    raw = raw.lstrip("*")
    if bv is not None:
        for prefix in ("_Z", "_ZTI"):
            name = _bn_demangle(bv, prefix + raw)
            if name:
                return name
    return demangle_typeinfo_name(raw)


def _fail(why, reason):
    if why is not None:
        why.append(reason)
    return None


class Itanium:
    name = "itanium"
    allocators = ALLOCATORS
    deallocators = DEALLOCATORS

    def __init__(self, bv, mem, log=print):
        self.bv = bv
        self.mem = mem
        self.log = log
        self._ti_cache = {}
        self._looks_cache = {}
        self._cluster_kind = {}   # typeinfo vptr value -> kind
        self._symbol_kind = {}    # typeinfo vptr value -> kind or None

    # ---- names -----------------------------------------------------------

    def _read_name(self, ti):
        name_ptr = self.mem.read_ptr(ti + self.mem.ptrsize)
        if not self.mem.is_data(name_ptr):
            return None
        raw = self.mem.read_cstring(name_ptr)
        if raw is None or len(raw) < 2:
            return None
        try:
            raw = raw.decode("ascii")
        except UnicodeDecodeError:
            return None
        if not _NAME_RE.match(raw):
            return None
        return raw

    def _looks_typeinfo(self, addr):
        if addr in self._looks_cache:
            return self._looks_cache[addr]
        ok = False
        if self.mem.is_data(addr):
            raw = self._read_name(addr)
            ok = raw is not None and demangle_name(self.bv, raw) is not None
        self._looks_cache[addr] = ok
        return ok

    # ---- kind identification --------------------------------------------

    def _kind_from_symbols(self, vptr):
        if vptr in self._symbol_kind:
            return self._symbol_kind[vptr]
        kind = None
        for probe in (vptr, vptr - 2 * self.mem.ptrsize):
            for sym in self.bv.get_symbols(probe, 1):
                raw = sym.raw_name
                if "__si_class_type_info" in raw:
                    kind = "si"
                elif "__vmi_class_type_info" in raw:
                    kind = "vmi"
                elif "__class_type_info" in raw:
                    kind = "class"
                if kind:
                    break
            if kind:
                break
        self._symbol_kind[vptr] = kind
        return kind

    def _structural_kind(self, ti):
        p = self.mem.ptrsize
        base = self.mem.read_ptr(ti + 2 * p)
        if self._looks_typeinfo(base):
            return "si"
        flags = self.mem.read_uint(ti + 2 * p, 4)
        count = self.mem.read_uint(ti + 2 * p + 4, 4)
        if flags is not None and count is not None and flags < 8 and 1 <= count <= MAX_BASES:
            first = self.mem.read_ptr(ti + 2 * p + 8)
            if self._looks_typeinfo(first):
                return "vmi"
        return "class"

    def prime(self, ti_addrs):
        """Vote a kind per typeinfo vptr value across all known objects, so a
        single ambiguous object cannot be misparsed in stripped binaries."""
        votes = {}
        for ti in ti_addrs:
            vptr = self.mem.read_ptr(ti)
            if not vptr:
                continue
            kind = self._structural_kind(ti)
            counts = votes.setdefault(vptr, {})
            counts[kind] = counts.get(kind, 0) + 1
        for vptr, counts in votes.items():
            self._cluster_kind[vptr] = max(counts.items(), key=lambda kv: kv[1])[0]

    def kind_of(self, ti):
        vptr = self.mem.read_ptr(ti)
        if vptr:
            kind = self._kind_from_symbols(vptr)
            if kind:
                return kind
            kind = self._cluster_kind.get(vptr)
            if kind:
                return kind
        return self._structural_kind(ti)

    # ---- parsing --------------------------------------------------------

    def parse_typeinfo(self, ti, depth=0):
        """Returns (name, [BaseRef]) or None."""
        if ti in self._ti_cache:
            return self._ti_cache[ti]
        self._ti_cache[ti] = None
        raw = self._read_name(ti)
        if raw is None:
            return None
        name = demangle_name(self.bv, raw) or raw.lstrip("*")
        p = self.mem.ptrsize
        kind = self.kind_of(ti)
        bases = []
        if kind == "si":
            bt = self.mem.read_ptr(ti + 2 * p)
            if self.mem.is_data(bt):
                sub = self.parse_typeinfo(bt, depth + 1) if depth < MAX_DEPTH else None
                bases.append(BaseRef(sub[0] if sub else None, 0, False, bt))
        elif kind == "vmi":
            count = self.mem.read_uint(ti + 2 * p + 4, 4) or 0
            for i in range(min(count, MAX_BASES)):
                entry = ti + 2 * p + 8 + i * 2 * p
                bt = self.mem.read_ptr(entry)
                of = self.mem.read_int(entry + p, p)
                if bt is None or of is None or not self.mem.is_data(bt):
                    break
                virtual = bool(of & 1)
                offset = of >> 8
                if not virtual and not 0 <= offset < MAX_OBJECT:
                    break
                sub = self.parse_typeinfo(bt, depth + 1) if depth < MAX_DEPTH else None
                bases.append(BaseRef(sub[0] if sub else None,
                                     None if virtual else offset, virtual, bt))
        result = (name, bases)
        self._ti_cache[ti] = result
        return result

    def parse_vtable_at(self, ap, why=None, trusted=False, bound=None):
        p = self.mem.ptrsize
        ott = self.mem.read_int(ap - 2 * p, p)
        ti_ptr = self.mem.read_ptr(ap - p)
        if ott is None or ti_ptr is None:
            return _fail(why, "header unreadable")
        if ott > 0 or ott < -MAX_OBJECT or ott % p != 0:
            return _fail(why, "offset-to-top %d implausible" % ott)
        name, bases = None, []
        if ti_ptr != 0:
            if not self.mem.is_data(ti_ptr):
                return _fail(why, "typeinfo pointer %#x not in data" % ti_ptr)
            parsed = self.parse_typeinfo(ti_ptr)
            if parsed is None:
                return _fail(why, "typeinfo %#x unparsable" % ti_ptr)
            name, bases = parsed
        # A vtable symbol vouches for the address point, so null slots read as
        # slots there too: abstract classes carry null destructor slots.
        limit = MAX_SLOTS if bound is None else max(0, min(MAX_SLOTS, (bound - ap) // p))
        slots, unresolved = read_slots(self.mem, ap, limit,
                                       allow_null=ti_ptr != 0 or trusted)
        if not slots or (ti_ptr == 0 and not trusted
                         and not any(s is not None for s in slots)):
            return _fail(why, "no function slots (%d pure)" % len(slots))
        return VtableInfo(address=ap, slots=slots,
                          typeinfo_addr=ti_ptr if ti_ptr else None,
                          object_offset=-ott, rtti_name=name,
                          bases=list(bases), unresolved=unresolved)

    def mark_construction_tables(self, tables, log=print):
        """Flag construction vtables: the tables a derived class D's
        constructors install while building a base T with virtual bases,
        laid out like T's own tables and carrying T's typeinfo, so they
        would pass for a second copy of T. Evidence, in order: a _ZTC
        symbol covering the table; a _ZTT symbol whose entries list the
        address point after D's own primary; without symbols, a VTT found
        by its shape, a run of pointers to known address points that starts
        with a primary of D and lists a primary of a base of D. Sets
        VtableInfo.construction to D's name."""
        p = self.mem.ptrsize
        by_ap = {t.address: t for t in tables}
        ti_name = {t.typeinfo_addr: t.rtti_name for t in tables if t.has_rtti}
        marked = {}

        def mark(t, derived, how):
            if t.construction is None:
                t.construction = derived
                marked[t.address] = how

        def vtt_entries(addr):
            out = []
            while True:
                val = self.mem.read_ptr(addr)
                if val is None or val not in by_ap:
                    return out
                out.append(by_ap[val])
                addr += p

        def mark_vtt(entries, derived, how):
            # The first entry is D's own primary; the primary tables that
            # follow with another class's typeinfo are construction vtables,
            # and the entries sharing that typeinfo at other offsets are
            # their secondaries.
            own = entries[0]
            ctor_tis = set()
            for t in entries[1:]:
                if t.has_rtti and t.typeinfo_addr != own.typeinfo_addr:
                    if t.object_offset == 0:
                        ctor_tis.add(t.typeinfo_addr)
                    if t.typeinfo_addr in ctor_tis:
                        mark(t, derived, how)

        data_syms = sorted((s.address, s.raw_name) for s in self.bv.get_symbols()
                           if s.type == SymbolType.DataSymbol)
        for i, (addr, raw) in enumerate(data_syms):
            if raw.startswith("_ZTC"):
                end = data_syms[i + 1][0] if i + 1 < len(data_syms) else addr + MAX_SLOTS * p
                for t in tables:
                    if t.has_rtti and addr <= t.address - 2 * p < end:
                        mark(t, self._ztc_derived(raw), "_ZTC symbol")
            elif raw.startswith("_ZTT"):
                entries = vtt_entries(addr)
                if len(entries) >= 2:
                    mark_vtt(entries, demangle_name(self.bv, raw[4:]), "_ZTT symbol")
        seen = set()
        for t in tables:
            for ref in self.bv.get_data_refs(t.address):
                if ref in seen or not self.mem.is_data(ref):
                    continue
                seen.add(ref)
                entries = vtt_entries(ref)
                if len(entries) < 2 or self.mem.read_ptr(ref - p) in by_ap:
                    continue
                own = entries[0]
                if not own.has_rtti or own.object_offset != 0:
                    continue
                base_tis = {b.typeinfo for b in own.bases}
                if any(e.has_rtti and e.object_offset == 0 and e.typeinfo_addr in base_tis
                       for e in entries[1:]):
                    mark_vtt(entries, own.rtti_name, "VTT shape")
        if marked:
            hows = sorted(set(marked.values()))
            log("[oorecover] %d construction vtables (%s)" % (len(marked), ", ".join(
                "%d by %s" % (sum(1 for h in marked.values() if h == how), how) for how in hows)))
        return marked

    def _ztc_derived(self, raw):
        """D of _ZTC<D><offset>_<T>: the derived class the construction
        vtable belongs to, a nested name or a plain length-prefixed one."""
        body = raw[4:]
        if body.startswith("N"):
            end = _skip_group(body, 0)
        else:
            end = _skip_ident(body, 0)
        return demangle_name(self.bv, body[:end])

    def read_virtual_bases(self, tables, log=print):
        """Record on each primary table the virtual bases of its class,
        direct or indirect, with the object offsets the header gives: one
        vbase offset entry per virtual base precedes offset-to-top, the
        primary base's entries first, then the class's own in inheritance
        graph order, nearest first (GCC and Clang agree). A virtual
        primary base puts vcall offsets in front of them, which RTTI does
        not reveal, so the entries count only when every polymorphic
        virtual base lands on a distinct secondary table of the group."""
        p = self.mem.ptrsize
        primaries = {}      # typeinfo -> primary table
        offsets = {}        # typeinfo -> object offsets of the group's tables
        for t in tables:
            if not t.has_rtti or t.construction:
                continue
            offsets.setdefault(t.typeinfo_addr, set()).add(t.object_offset)
            if t.object_offset == 0:
                primaries.setdefault(t.typeinfo_addr, t)
        with_vbases = trusted = 0
        for ti, prim in primaries.items():
            order = self._vbase_order(ti, primaries)
            if not order:
                continue
            with_vbases += 1
            found = []
            for i, v in enumerate(order):
                off = self.mem.read_int(prim.address - (3 + i) * p, p)
                if off is None or off < 0 or off >= MAX_OBJECT:
                    break
                if v.typeinfo in primaries and (off == 0 or off not in offsets[ti]):
                    break
                found.append(off)
            landed = [found[i] for i, v in enumerate(order) if i < len(found) and v.typeinfo in primaries]
            ok = len(found) == len(order) and len(set(landed)) == len(landed)
            trusted += ok
            prim.vbases = [BaseRef(v.name, found[i] if ok else None, True, v.typeinfo)
                           for i, v in enumerate(order)]
        if with_vbases:
            log("[oorecover] %d classes with virtual bases, %d with vbase offsets read from the vtable header"
                % (with_vbases, trusted))

    def _vbase_order(self, ti, primaries, depth=0, out=None, seen=None):
        """Virtual bases of the class ti describes in vbase offset order:
        those of its primary base (the first non-virtual polymorphic base
        at offset 0) first, then its own, each once, in inheritance graph
        order: a depth-first walk of the RTTI bases in declaration order."""
        out = [] if out is None else out
        seen = set() if seen is None else seen
        parsed = self.parse_typeinfo(ti)
        if parsed is None or depth > MAX_DEPTH:
            return out
        primary = next((b for b in parsed[1]
                        if not b.virtual and b.offset == 0 and b.typeinfo in primaries), None)
        if primary is not None:
            self._vbase_order(primary.typeinfo, primaries, depth + 1, out, seen)
        for v in self._preorder_vbases(ti):
            if v.typeinfo not in seen:
                seen.add(v.typeinfo)
                out.append(v)
        return out

    def _preorder_vbases(self, ti, depth=0, out=None, visited=None):
        # A second walk of a class finds no virtual base the first missed.
        out = [] if out is None else out
        visited = set() if visited is None else visited
        parsed = self.parse_typeinfo(ti)
        if parsed is None or depth > MAX_DEPTH:
            return out
        for b in parsed[1]:
            if b.typeinfo in visited:
                continue
            visited.add(b.typeinfo)
            if b.virtual:
                out.append(b)
            self._preorder_vbases(b.typeinfo, depth + 1, out, visited)
        return out

    def symbol_candidates(self):
        p = self.mem.ptrsize
        for sym in self.bv.get_symbols():
            raw = sym.raw_name
            if not raw.startswith("_ZTV") or raw.startswith("_ZTVN10__cxxabiv1"):
                continue
            if sym.type != SymbolType.DataSymbol:
                continue
            # Tables of classes with virtual bases start with vbase offsets;
            # probe a few address points past the header.
            for k in range(2, 6):
                yield sym.address + k * p, sym.address, raw

    def symbol_class(self, raw):
        """Class of a vtable symbol: what follows _ZTV is the mangled type.
        Names classes built without RTTI, whose tables carry no typeinfo."""
        return demangle_name(self.bv, raw[4:]) if raw.startswith("_ZTV") else None

    def is_rtti_header_ref(self, val):
        """True when val points at a typeinfo object (the word before an
        address point)."""
        if self._ti_cache.get(val) is not None:
            return True
        return self._looks_typeinfo(val)

    def typeinfo_addrs_of(self, candidates):
        p = self.mem.ptrsize
        out = set()
        for ap in candidates:
            ti = self.mem.read_ptr(ap - p)
            if ti and self.mem.is_data(ti):
                out.add(ti)
        return out
