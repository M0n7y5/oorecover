"""Itanium C++ ABI: vtable layout, RTTI parsing, typeinfo-name demangling.

Reference: https://itanium-cxx-abi.github.io/cxx-abi/abi.html#rtti
Vtable layout around the address point AP (ptr = pointer size):
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
from .names import demangle

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

    def _in_construction_vtable(self, ap):
        try:
            dv = self.bv.get_data_var_at(ap)
            sym = dv.symbol if dv is not None else None
            return sym is not None and sym.raw_name.startswith("_ZTC")
        except Exception:
            return False

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
            if self._in_construction_vtable(ap):
                return _fail(why, "inside a construction vtable")
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
