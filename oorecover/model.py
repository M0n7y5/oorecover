"""Build class models from vtables and collected facts (sure facts only).

Rules:
- Vtables sharing one typeinfo belong to one class; the table with object
  offset 0 is primary. Secondary tables are kept only where RTTI places a
  base (or the class has virtual bases), which excludes construction vtables.
- A function that stores vtables through its own this-pointer is a
  constructor or destructor. Constructors store the derived-most vtable
  last, destructors first; the other stores at the same offset come from
  inlined base constructors and name bases.
- Each virtual function is owned by the base-most class whose primary table
  lists it; functions only found in secondary tables are thunks.
- Members come from this-relative accesses in owned functions, and from
  construction sites (allocations and stack objects) bounded by the object
  size known for the class.
"""
import re

from binaryninja.enums import TypeClass

from .facts import BaseRef
from .names import mangled_class, member
from . import validate

_MARKER = re.compile(r"(C[123]|D[012])E")


def _skip_ident(raw, pos):
    m = re.match(r"\d+", raw[pos:])
    return pos + len(m.group(0)) + int(m.group(0))


_STD_ABBREV = "tabsiod"


def _skip_substitution(raw, pos):
    """S_ / S<seq>_ substitutions and the two-letter St/Sa/Sb/Ss/Si/So/Sd forms."""
    if pos + 1 < len(raw) and raw[pos + 1] in _STD_ABBREV:
        return pos + 2
    end = raw.find("_", pos)
    return len(raw) if end < 0 else end + 1


def _skip_group(raw, pos):
    """Skip a group opened at pos by I (template args) or N (nested name) or
    L (literal) up to and including its closing E, honouring length-prefixed
    identifiers, which may contain E/I/N."""
    depth = 0
    while pos < len(raw):
        ch = raw[pos]
        if ch.isdigit():
            pos = _skip_ident(raw, pos)
        elif ch in "INL":
            depth += 1
            pos += 1
            if ch == "L" and raw.startswith("_Z", pos):
                pos += 2
        elif ch == "E":
            depth -= 1
            pos += 1
            if depth == 0:
                return pos
        elif ch == "S":
            pos = _skip_substitution(raw, pos)
        else:
            pos += 1
    return pos


def _skip_template_args(raw, pos):
    return _skip_group(raw, pos)


def _itanium_role(raw):
    """Walk the nested-name components of a mangled name; constructor and
    destructor markers are the only components without a length prefix."""
    if not raw.startswith("_ZN"):
        return None
    pos = 3
    while pos < len(raw):
        ch = raw[pos]
        if ch.isdigit():
            pos = _skip_ident(raw, pos)
            continue
        m = _MARKER.match(raw, pos)
        if m:
            return "ctor" if m.group(1)[0] == "C" else "dtor"
        if ch == "I":
            pos = _skip_template_args(raw, pos)
            continue
        if raw.startswith("St", pos) or ch in "KVr":
            pos += 2 if raw.startswith("St", pos) else 1
            continue
        if ch == "S":
            pos = _skip_substitution(raw, pos)
            continue
        return None
    return None


class ClassModel:
    __slots__ = ("name", "typeinfo", "has_rtti", "vtables", "methods", "thunks",
                 "ctors", "dtors", "members", "bases", "size", "sites", "plain", "shared",
                 "embedded", "site_functions")

    def __init__(self, name, typeinfo=None, plain=False):
        self.name = name
        self.typeinfo = typeinfo
        self.has_rtti = typeinfo is not None
        self.plain = plain     # no vtable: known only through its named members
        self.vtables = {}      # object offset -> VtableInfo
        self.methods = set()   # owned virtual functions (primary table)
        self.thunks = {}       # function -> object offset of its secondary table
        self.shared = {}       # function -> slot: one implementation folded from
                               # several descendants, typed with this ancestor
        self.ctors = set()
        self.dtors = set()
        self.members = {}      # offset -> [size, hint, writes, reads]
        self.embedded = {}     # offset -> class of a member object built there
        self.bases = []        # [BaseRef]
        self.size = 0
        self.sites = 0         # construction sites seen
        self.site_functions = []   # (function, root) of each site

    def add_member(self, offset, size, hint, is_write):
        if offset < 0 or size <= 0 or offset in self.vtables:
            return
        m = self.members.get(offset)
        if m is None:
            self.members[offset] = [size, hint, int(is_write), int(not is_write)]
            return
        m[0] = max(m[0], size)
        if hint == "ptr":
            m[1] = "ptr"
        m[2] += int(is_write)
        m[3] += int(not is_write)

    def add_base(self, name, offset, virtual=False, typeinfo=None):
        for b in self.bases:
            if b.name == name and (b.offset == offset or (b.virtual and virtual)):
                return
        self.bases.append(BaseRef(name, offset, virtual, typeinfo))

    def extent(self, ptrsize, by_name):
        end = 0
        for off, m in self.members.items():
            end = max(end, off + m[0])
        for off in self.vtables:
            end = max(end, off + ptrsize)
        for b in self.bases:
            if b.offset is not None and b.name in by_name:
                end = max(end, b.offset + by_name[b.name].size)
        for off, name in self.embedded.items():
            if name in by_name:
                end = max(end, off + by_name[name].size)
        return max(self.size, end)

    def owns(self):
        return self.methods | self.ctors | self.dtors


def ancestors(cls, by_name, depth=0):
    out = {cls.name}
    if depth > 32:
        return out
    for b in cls.bases:
        bc = by_name.get(b.name)
        if bc is not None and bc is not cls:
            out |= ancestors(bc, by_name, depth + 1)
    return out


def common_ancestor(classes, by_name):
    """The most derived class every one of `classes` derives from (or is)."""
    common = None
    for c in classes:
        a = ancestors(c, by_name)
        common = a if common is None else common & a
    cands = [by_name[n] for n in (common or ()) if n in by_name]
    for c in cands:
        if all(o is c or derives_from(c, o, by_name) for o in cands):
            return c
    return None


def derives_from(cls, other, by_name, depth=0):
    if depth > 32:
        return False
    for b in cls.bases:
        if b.name == other.name:
            return True
        bc = by_name.get(b.name)
        if bc is not None and bc is not cls and derives_from(bc, other, by_name, depth + 1):
            return True
    return False


def base_at(cls, off, by_name, depth=0):
    """Name of the base class whose sub-object starts at `off` in cls."""
    if depth > 32:
        return None
    for b in cls.bases:
        if b.offset is None or b.name is None:
            continue
        if b.offset == off:
            return b.name
        bc = by_name.get(b.name)
        if bc is not None and b.offset < off:
            inner = base_at(bc, off - b.offset, by_name, depth + 1)
            if inner is not None:
                return inner
    return None


def topo_order(classes):
    """Bases and embedded objects before the classes holding them; ties
    broken by primary table length, then name."""
    by_name = {c.name: c for c in classes}
    order, seen = [], set()

    def visit(c):
        if c.name in seen:
            return
        seen.add(c.name)
        for name in [b.name for b in c.bases] + list(c.embedded.values()):
            bc = by_name.get(name)
            if bc is not None:
                visit(bc)
        order.append(c)

    def slots(c):
        return len(c.vtables[0].slots) if 0 in c.vtables else 0

    for c in sorted(classes, key=lambda c: (slots(c), c.name)):
        visit(c)
    return order


_THUNK_SHIFT = re.compile(r"^_ZThn(\d+)_")


def symbol_thunk_shift(bv, addr):
    """this-adjustment of a non-virtual thunk symbol, -1 for a virtual thunk
    (adjustment only known at runtime), None for ordinary functions."""
    sym = bv.get_symbol_at(addr)
    if sym is None:
        return None
    raw = sym.raw_name
    m = _THUNK_SHIFT.match(raw)
    if m:
        return int(m.group(1))
    if raw.startswith("_ZTv"):
        return -1
    return None


def symbol_role(bv, addr):
    """'ctor' or 'dtor' when the function's mangled name says so, else None."""
    sym = bv.get_symbol_at(addr)
    if sym is None:
        return None
    raw = sym.raw_name
    if raw.startswith("_Z"):
        return _itanium_role(raw)
    if raw.startswith("??0"):
        return "ctor"
    if raw.startswith(("??1", "??_G", "??_E")):
        return "dtor"
    return None


def structor_class_names(bv, facts, wanted, log=print):
    """Vtable address -> class name, read from constructor and destructor
    symbols. A constructor stores its own class's table into a sub-object
    last, a destructor first; the stores around it belong to the bases the
    compiler inlined. Names classes whose tables carry neither RTTI nor a
    vtable symbol.
    """
    if not wanted:
        return {}
    votes = {}
    for faddr, ff in facts.items():
        installs = [i for i in ff.installs if i.offset == 0 and i.vtable in wanted]
        if not installs:
            continue
        role = symbol_role(bv, faddr)
        if role is None or symbol_thunk_shift(bv, faddr) is not None:
            continue
        func = bv.get_function_at(faddr)
        name = mangled_class(bv, func) if func is not None else None
        if name is None:
            continue
        own = {}
        for i in ff.installs:
            if i.offset != 0:
                continue
            prev = own.get(i.root)
            if prev is None or (i.order > prev.order if role == "ctor" else i.order < prev.order):
                own[i.root] = i
        for i in own.values():
            if i.vtable in wanted:
                votes.setdefault(i.vtable, {}).setdefault(name, 0)
                votes[i.vtable][name] += 1
    named = {}
    for vtable, counts in votes.items():
        ranked = sorted(counts.items(), key=lambda kv: -kv[1])
        if len(ranked) == 1 or ranked[0][1] > ranked[1][1]:
            named[vtable] = ranked[0][0]
        else:
            log("[oorecover] table %#x: constructors of %s disagree; unnamed"
                % (vtable, ", ".join(sorted(counts))))
    return named


def _has_ref(bv, addr):
    for _ref in bv.get_code_refs(addr, max_items=1):
        return True
    return False


def build_model(bv, mem, tables, facts, log=print):
    ptrsize = mem.ptrsize
    table_at = {t.address: t for t in tables}
    classes = []
    owner = {}          # vtable address -> ClassModel
    names = set()

    def unique(name, addr):
        if name in names:
            name = "%s_%x" % (name, addr)
        names.add(name)
        return name

    def add_group(cls, group, base_offsets=None):
        """Attach a class's tables by sub-object offset. Tables at an offset
        no base explains come from a neighbouring class whose symbol or
        typeinfo they share; only RTTI names the offsets, so unnamed groups
        keep every table they carry."""
        for t in group:
            off = t.object_offset
            if base_offsets is not None and off != 0 and off not in base_offsets:
                log("[oorecover] %s: table %#x at offset %d has no base there; ignored"
                    % (cls.name, t.address, off))
                continue
            prev = cls.vtables.get(off)
            if prev is not None:
                if _has_ref(bv, prev.address) or not _has_ref(bv, t.address):
                    continue
                owner.pop(prev.address, None)
            cls.vtables[off] = t
            owner[t.address] = cls
        classes.append(cls)

    def group_by(key):
        groups = {}
        for t in tables:
            k = key(t)
            if k is not None:
                groups.setdefault(k, []).append(t)
        out = []
        for k, group in sorted(groups.items()):
            group.sort(key=lambda t: (t.object_offset, t.address))
            out.append((k, group, next((t for t in group if t.object_offset == 0), group[0])))
        return out

    for ti, group, primary in group_by(lambda t: t.typeinfo_addr if t.has_rtti else None):
        cls = ClassModel(unique(primary.rtti_name or "class_%x" % primary.address,
                                primary.address), ti)
        cls.bases = [BaseRef(b.name, b.offset, b.virtual, b.typeinfo) for b in primary.bases]
        offsets = {b.offset for b in cls.bases if b.offset is not None}
        add_group(cls, group, None if any(b.virtual for b in cls.bases) else offsets)

    for _sym, group, primary in group_by(
            lambda t: t.sym_addr if not t.has_rtti and t.sym_name else None):
        add_group(ClassModel(unique(primary.sym_name, primary.address)), group)

    installed = {i.vtable for ff in facts.values() for i in ff.installs}
    unnamed = {t.address for t in tables
               if not t.has_rtti and not t.sym_name and t.address in installed}
    structor_names = structor_class_names(bv, facts, unnamed, log)
    provisional_dropped = 0
    for t in tables:
        if t.has_rtti or t.sym_name:
            continue
        if t.address not in installed:
            provisional_dropped += 1
            continue
        name = structor_names.get(t.address) or "class_%x" % t.address
        cls = ClassModel(unique(name, t.address))
        cls.vtables[0] = t
        owner[t.address] = cls
        classes.append(cls)
    if provisional_dropped:
        log("[oorecover] %d RTTI-less candidates never installed; dropped" % provisional_dropped)

    def primary_table(cls):
        if 0 in cls.vtables:
            return cls.vtables[0]
        return cls.vtables[min(cls.vtables)] if cls.vtables else None

    by_name = {c.name: c for c in classes}

    def derived_most(cands):
        uniq = []
        for c in cands:
            if c not in uniq:
                uniq.append(c)
        if len(uniq) == 1:
            return uniq[0]
        for c in uniq:
            if all(o is c or derives_from(c, o, by_name) for o in uniq):
                return c
        return max(uniq, key=lambda c: len(c.vtables[0].slots) if 0 in c.vtables else 0)

    def absorb(own, by_off, role):
        """own claims the last (ctor) or first (dtor) table stored at each
        offset; the other tables stored there come from inlined base
        constructors and name bases at that offset."""
        for off, lst in by_off.items():
            ordered = lst if role == "ctor" else list(reversed(lst))
            own_t = table_at[ordered[-1].vtable]
            own_cls = owner[own_t.address]
            if own_cls is not own and off > 0 and not own_cls.has_rtti \
                    and list(own_cls.vtables) == [0] and not own_cls.ctors and not own_cls.dtors:
                own.vtables[off] = own_t
                owner[own_t.address] = own
                classes.remove(own_cls)
                del by_name[own_cls.name]
            if own.has_rtti or off < 0:
                continue
            for earlier in ordered[:-1]:
                bc = owner[earlier.vtable]
                if bc is not own:
                    own.add_base(bc.name, off)

    def group_installs(installs):
        by_off = {}
        for inst in sorted(installs, key=lambda i: i.order):
            by_off.setdefault(inst.offset, []).append(inst)
        return by_off

    virtual_of = {}    # function -> (class, table offset, reached via thunk)
    for cls in classes:
        for off, t in sorted(cls.vtables.items()):
            for fn in t.functions:
                virtual_of.setdefault(fn, (cls, off, False))
                ff = facts.get(fn)
                if ff is not None and ff.tail_target is not None:
                    virtual_of.setdefault(ff.tail_target, (cls, off, True))

    def has_base_at(cls, base, off, depth=0):
        if depth > 32:
            return False
        for b in cls.bases:
            if b.offset is None:
                continue
            bc = by_name.get(b.name)
            if bc is None:
                continue
            if bc is base and b.offset == off:
                return True
            if off >= b.offset and has_base_at(bc, base, off - b.offset, depth + 1):
                return True
        return False

    def layout_owner(by_off):
        """The unique class whose own tables and known bases explain the last
        table stored at every offset; None when ambiguous."""
        stored = {off: owner[lst[-1].vtable] for off, lst in by_off.items()}
        matches = []
        for cls in classes:
            if all((sc is cls and off in cls.vtables) or has_base_at(cls, sc, off)
                   for off, sc in stored.items()):
                matches.append(cls)
        return matches[0] if len(matches) == 1 else None

    for faddr, ff in facts.items():
        this_installs = [i for i in ff.installs if i.root == ("this",) and i.vtable in owner]
        if not this_installs:
            continue
        by_off = group_installs(this_installs)
        hint = symbol_role(bv, faddr)
        positive = {off: lst for off, lst in by_off.items() if off >= 0}
        shift = symbol_thunk_shift(bv, faddr)
        if shift is not None or (min(by_off) < 0 and hint != "ctor"):
            # A thunk that adjusted this downwards and fell through into the
            # destructor body stores at offsets relative to the sub-object.
            # Objects with a header below this (engine allocators) also store
            # at negative offsets, so without a symbol the shifted layout has
            # to match a known class before it counts as a thunk.
            if shift is None or shift < 0:
                shift = -min(by_off) if min(by_off) < 0 else 0
            shifted = {off + shift: lst for off, lst in by_off.items()}
            matched = layout_owner(shifted) if 0 in shifted else None
            if matched is not None or not positive or symbol_thunk_shift(bv, faddr) is not None:
                cands = [owner[i.vtable] for i in shifted[0]] if 0 in shifted else []
                own = matched or (derived_most(cands) if cands else None)
                if own is not None:
                    own.dtors.add(faddr)
                    own.thunks[faddr] = shift
                    continue
        if not positive:
            continue
        base_off = 0 if 0 in positive else min(positive)
        cands = [owner[i.vtable] for i in positive[base_off]]
        if hint == "ctor":
            own = derived_most(cands)
            own.ctors.add(faddr)
            absorb(own, positive, "ctor")
            continue
        if faddr in virtual_of:
            own, table_off, via_thunk = virtual_of[faddr]
            own.dtors.add(faddr)
            if not via_thunk and table_off == 0:
                absorb(own, positive, "dtor")
            continue
        matched = layout_owner(positive)
        if matched is not None and matched not in cands:
            matched.dtors.add(faddr)
            continue
        own = matched or derived_most(cands)
        if hint == "dtor":
            role = "dtor"
        elif len(cands) == 1 or cands[-1] is own:
            role = "ctor"
        elif cands[0] is own:
            role = "dtor"
        else:
            continue
        (own.ctors if role == "ctor" else own.dtors).add(faddr)
        absorb(own, positive, role)

    sites = []
    instances = {}      # address of a static object -> class constructed there
    for faddr, ff in facts.items():
        roots = {}
        for inst in ff.installs:
            if inst.root[0] in ("alloc", "stack", "global") and inst.vtable in owner:
                roots.setdefault(inst.root, []).append(inst)
        for root, installs in roots.items():
            by_off = group_installs(installs)
            if 0 not in by_off:
                continue
            cands = [owner[i.vtable] for i in by_off[0]]
            own = derived_most(cands)
            if cands[-1] is not own:
                continue
            absorb(own, by_off, "ctor")
            if root[0] == "global":
                # A constructor storing a table into a fixed address builds a
                # static instance there (a global, a singleton).
                instances[root[1]] = own
            else:
                sites.append((faddr, root, own))

    for cls in classes:
        prim = primary_table(cls)
        if prim is None:
            continue
        for fn in prim.functions:
            ff = facts.get(fn)
            if ff is None:
                continue
            this_calls = [c for c in ff.calls if c.root == ("this",) and c.offset == 0]
            if not any(c.dealloc for c in this_calls):
                continue
            cls.dtors.add(fn)
            cls.ctors.discard(fn)
            for c in this_calls:
                if c.dealloc or c.callee == fn:
                    continue
                holder = next((o for o in classes if c.callee in o.ctors), None)
                if holder is not None:
                    holder.ctors.discard(c.callee)
                    cls.dtors.add(c.callee)
                elif c.callee in prim.functions or not any(c.callee in o.dtors for o in classes):
                    cls.dtors.add(c.callee)

    plain = plain_classes(bv, facts, names, log)
    classes.extend(plain)
    names.update(c.name for c in plain)

    def named_class(fn):
        if symbol_thunk_shift(bv, fn) is not None or symbol_role(bv, fn) is None:
            return None
        func = bv.get_function_at(fn)
        return mangled_class(bv, func) if func is not None else None

    findings = validate.check_roles(classes, log, named_class)
    ctor_of = {fn: c for c in classes for fn in c.ctors}
    dtor_of = {fn: c for c in classes for fn in c.dtors}

    seen_sites = set()
    for faddr, ff in facts.items():
        for call in ff.calls:
            if call.root[0] not in ("alloc", "stack", "global") or call.offset != 0:
                continue
            if (faddr, call.root) in seen_sites or any(
                    s[0] == faddr and s[1] == call.root for s in sites):
                continue
            cls = ctor_of.get(call.callee)
            if cls is None:
                continue
            seen_sites.add((faddr, call.root))
            if call.root[0] == "global":
                # A constructor called on a fixed address: a static instance
                # built by the startup code.
                instances.setdefault(call.root[1], cls)
            else:
                sites.append((faddr, call.root, cls))
    if instances:
        log("[oorecover] %d static instances" % len(instances))

    order = topo_order(classes)
    claimed = {}
    for cls in order:
        for fn in cls.ctors | cls.dtors:
            claimed.setdefault(fn, cls)
    for cls in order:
        if cls.plain:
            for fn in cls.methods:
                claimed.setdefault(fn, cls)
    # One function listed by classes that are not related by inheritance is
    # one implementation folded from several (identical code, empty
    # destructors). It is a method of their common ancestor when there is
    # one, and of nobody otherwise: it must not type this or name members.
    listed = {}
    for cls in order:
        t = primary_table(cls)
        if t is not None:
            for fn in t.functions:
                listed.setdefault(fn, []).append(cls)
    shared = {}
    for fn, owners in listed.items():
        if len(owners) < 2 or fn in claimed:
            continue
        tops = [c for c in owners
                if not any(o is not c and derives_from(c, o, by_name) for o in owners)]
        # Unrelated is only meaningful where ancestry is known: a class
        # without RTTI and without an inferred base may simply be a base we
        # could not connect (inlined constructors), so the first table keeps
        # the function as before.
        if len(tops) >= 2 and all(c.has_rtti or c.bases for c in tops):
            shared[fn] = (tops, common_ancestor(tops, by_name))
    for fn, (tops, common) in shared.items():
        if common is not None:
            claimed[fn] = common
            common.shared[fn] = next(
                (i for i, f in enumerate(primary_table(tops[0]).slots) if f == fn), 0)
    unowned = {fn: tops for fn, (tops, common) in shared.items() if common is None}
    if shared:
        log("[oorecover] %d shared implementations (%d typed with a common base)"
            % (len(shared), len(shared) - len(unowned)))
    for cls in order:
        t = primary_table(cls)
        if t is None:
            continue
        for fn in t.functions:
            if fn not in claimed and fn not in shared:
                claimed[fn] = cls
                cls.methods.add(fn)
    for cls in order:
        prim = primary_table(cls)
        for off, t in cls.vtables.items():
            if t is prim:
                continue
            for fn in t.functions:
                if fn not in claimed and fn not in shared:
                    claimed[fn] = cls
                    cls.thunks[fn] = off
    for fn, (cls, off, via_thunk) in virtual_of.items():
        if via_thunk and fn not in shared and (fn not in claimed or claimed[fn] is cls):
            claimed.setdefault(fn, cls)
            cls.thunks[fn] = off

    for cls in order:
        for fn in cls.owns():
            ff = facts.get(fn)
            if ff is None or fn in cls.thunks:
                continue
            for a in ff.accesses:
                if a.root == ("this",):
                    cls.add_member(a.offset, a.size, a.hint, a.is_write)
            if fn in cls.ctors or fn in cls.dtors:
                cls.size = max(cls.size, ff.reach)

    stack_roots = {}
    alloc_sizes = {}    # class -> smallest allocation constructed as that class
    for faddr, root, cls in sites:
        ff = facts[faddr]
        cls.sites += 1
        cls.site_functions.append((faddr, root))
        if root[0] == "alloc":
            alloc = next((a for a in ff.allocs if a.insn == root[1]), None)
            bound = alloc.size if alloc is not None else None
            if bound is not None:
                cls.size = max(cls.size, bound)
                alloc_sizes[cls.name] = min(alloc_sizes.get(cls.name, bound), bound)
            for a in ff.accesses:
                if a.root == root and (bound is None or a.offset + a.size <= bound):
                    cls.add_member(a.offset, a.size, a.hint, a.is_write)
        else:
            stack_roots.setdefault(faddr, []).append((root[1], cls))

    for cls in order:
        cls.size = cls.extent(ptrsize, by_name)

    for faddr, lst in stack_roots.items():
        ff = facts[faddr]
        lst.sort(key=lambda e: e[0])
        for idx, (storage, cls) in enumerate(lst):
            bound = cls.size
            if idx + 1 < len(lst):
                bound = min(bound, lst[idx + 1][0] - storage)
            for _insn, st, size, is_write in ff.stack_accesses:
                off = st - storage
                if 0 <= off and off + size <= bound:
                    cls.add_member(off, size, "int", is_write)

    # Constructors and destructors called on this+offset build the bases and
    # the embedded objects of a class without RTTI. Bases come first and lie
    # end to end from offset 0 (alignment padding aside); anything called
    # further in is a member object. A sub-object with its own table here is
    # a base wherever it sits (a virtual base follows the members).
    for cls in classes:
        for fn in sorted(cls.ctors | cls.dtors):
            ff = facts.get(fn)
            if ff is None:
                continue
            expected = 0
            for b in cls.bases:
                bc = by_name.get(b.name)
                if b.offset is not None and bc is not None:
                    expected = max(expected, b.offset + bc.size)
            for call in sorted(ff.calls, key=lambda c: c.insn if fn in cls.ctors else -c.insn):
                if call.root != ("this",) or call.offset < 0 or call.dealloc:
                    continue
                target = ctor_of.get(call.callee) or dtor_of.get(call.callee)
                if target is None or target is cls:
                    continue
                off = call.offset
                if cls.has_rtti:
                    # RTTI lists the bases; a constructor called elsewhere
                    # builds a member object.
                    if not any(b.offset is not None and b.offset <= off < b.offset + max(by_name[b.name].size, 1)
                               for b in cls.bases if b.name in by_name) \
                            and not any(b.virtual for b in cls.bases) and off not in cls.embedded:
                        cls.embedded[off] = target.name
                elif off == 0 or off in cls.vtables or expected <= off <= (expected + 15) & ~15:
                    cls.add_base(target.name, off)
                    expected = max(expected, off + target.size)
                elif off not in cls.embedded:
                    cls.embedded[off] = target.name

    findings += validate.check_structure(topo_order(classes), alloc_sizes,
                                lambda c: c.extent(ptrsize, by_name), log)

    vcalls, param_classes = resolve_virtual_calls(bv, classes, facts, claimed, sites, by_name, log,
                                                  unowned)
    if len(vcalls) <= 12:
        for caller, insn, cls_name, exact, targets in vcalls:
            log("[oorecover]   vcall %#x in %#x: %s%s -> %s" % (
                insn, caller, cls_name, " (exact)" if exact else "",
                ", ".join("%#x" % t for t in targets)))

    classes.sort(key=lambda c: c.name)
    log("[oorecover] model: %d classes, %d ctors, %d dtors, %d with bases, %d sites, "
        "%d virtual calls resolved (%d targets)"
        % (len(classes), sum(len(c.ctors) for c in classes),
           sum(len(c.dtors) for c in classes), sum(1 for c in classes if c.bases),
           len(sites), len(vcalls), sum(len(v[4]) for v in vcalls)))
    return classes, vcalls, param_classes, {
        "findings": findings, "unowned": unowned,
        "instances": {addr: c.name for addr, c in instances.items()}}


MAX_PLAIN_MEMBER_GAP = 1 << 16


def plain_classes(bv, facts, taken, log=print):
    """Classes with no vtable, known only through mangled member functions
    that read this. Constructors and destructors come from their mangled
    roles; every other member reading this is a method."""
    groups = {}
    for faddr, ff in facts.items():
        if ff.member_of is None or ff.member_of in taken or not ff.entry_this:
            continue
        groups.setdefault(ff.member_of, []).append(faddr)
    out = []
    for name, fns in sorted(groups.items()):
        cls = ClassModel(name, plain=True)
        for fn in fns:
            role = symbol_role(bv, fn)
            if role == "ctor":
                cls.ctors.add(fn)
            elif role == "dtor":
                cls.dtors.add(fn)
            else:
                cls.methods.add(fn)
        out.append(cls)
    log("[oorecover] plain classes (no vtable): %d from %d member functions"
        % (len(out), sum(len(f) for f in groups.values())))
    return out


def base_offset_in(derived, base, by_name, depth=0):
    """Offset of the (non-virtual) base sub-object of `base` inside `derived`,
    or None when base is not a non-virtual ancestor."""
    if depth > 32:
        return None
    for b in derived.bases:
        if b.offset is None:
            continue
        bc = by_name.get(b.name)
        if bc is None:
            continue
        if bc is base:
            return b.offset
        inner = base_offset_in(bc, base, by_name, depth + 1)
        if inner is not None:
            return b.offset + inner
    return None


def resolve_virtual_calls(bv, classes, facts, claimed, sites, by_name, log=print, unowned=()):
    """Resolve indirect calls through vtables to their implementations.

    Returns [(caller, insn, static class name, exact, [targets])]. A call
    through this inside a constructor or destructor, or on an object created
    at a known site, has an exact dynamic type; a call inside an ordinary
    method resolves to the class's slot and every subclass override of it.
    """
    subclasses = {c.name: [] for c in classes}
    for c in classes:
        for b in c.bases:
            if b.name in subclasses:
                subclasses[b.name].append(c)

    def descendants(cls):
        out, stack, seen = [], list(subclasses.get(cls.name, [])), set()
        while stack:
            d = stack.pop()
            if d.name in seen:
                continue
            seen.add(d.name)
            out.append(d)
            stack.extend(subclasses.get(d.name, []))
        return out

    site_class = {(faddr, root): cls for faddr, root, cls in sites}
    param_class = infer_param_classes(bv, classes, facts, claimed, site_class, by_name, log,
                                      unowned)
    def targets_for(cls, vc, exact):
        table = cls.vtables.get(vc.object_offset)
        if table is None or vc.slot >= len(table.slots):
            return []
        targets = []
        own = table.slots[vc.slot]
        if own is not None:
            targets.append(own)
        if not exact:
            for d in descendants(cls):
                off = base_table_offset(d, cls, by_name)
                if off is None:
                    continue
                t = d.vtables.get(off + vc.object_offset)
                if t is None or vc.slot >= len(t.slots):
                    continue
                fn = t.slots[vc.slot]
                if fn is not None and fn not in targets:
                    targets.append(fn)
        return targets

    resolved = []
    for faddr, ff in facts.items():
        if not ff.vcalls:
            continue
        owner_cls = claimed.get(faddr)
        for vc in ff.vcalls:
            if vc.root == ("this",) and faddr in unowned:
                # One implementation serving unrelated classes: this is an
                # object of any of them, so the call reaches every one's slot.
                targets = []
                for top in unowned[faddr]:
                    targets.extend(t for t in targets_for(top, vc, False) if t not in targets)
                if targets:
                    resolved.append((faddr, vc.insn, "|".join(t.name for t in unowned[faddr]),
                                     False, targets))
                continue
            if vc.root == ("this",) and owner_cls is not None:
                cls = owner_cls
                if faddr in cls.thunks:
                    continue
                exact = faddr in cls.ctors or faddr in cls.dtors
            elif vc.root[0] in ("alloc", "stack"):
                cls = site_class.get((faddr, vc.root))
                exact = True
            elif vc.root == ("this",) or vc.root[0] == "param":
                index = 0 if vc.root == ("this",) else vc.root[1]
                cls, _source, alt = param_class.get((faddr, index), (None, None, None))
                exact = False
                # A slot beyond the declared type's table proves the declared
                # type too weak (stale or a base); the class callers pass wins.
                if cls is not None and alt is not None and derives_from(alt, cls, by_name):
                    table = cls.vtables.get(vc.object_offset)
                    if table is None or vc.slot >= len(table.slots):
                        cls = alt
            else:
                continue
            if cls is None:
                if len(facts) <= 64:
                    log("[oorecover]   vcall %#x in %#x: root %s unresolved" % (vc.insn, faddr, vc.root))
                continue
            targets = targets_for(cls, vc, exact)
            if targets:
                resolved.append((faddr, vc.insn, cls.name, exact, targets))
    inferred = {k: v[0].name for k, v in param_class.items() if v[1] == "argpass"}
    if len(param_class) <= 32:
        for (faddr, index), (cls, source, alt) in sorted(param_class.items()):
            log("[oorecover]   param %#x:%d -> %s (%s%s)" % (
                faddr, index, cls.name, source, ", callers pass " + alt.name if alt else ""))
    return resolved, inferred


def infer_param_classes(bv, classes, facts, claimed, site_class, by_name, log=print, unowned=()):
    """(function, parameter index) -> (class, source, alt) for parameters
    that point to a known class: from the Binary Ninja signature when it
    names one ("type"), else from the objects callers pass in ("argpass"),
    taking the common ancestor of every root class observed. alt is the
    argpass class when the signature already named one."""
    out = {}
    for faddr, ff in facts.items():
        if not ff.vcalls:
            continue
        func = bv.get_function_at(faddr)
        if func is None:
            continue
        try:
            params = list(func.type.parameters)
        except Exception:
            continue
        # Pre-6.0 demangled member signatures omit this: declared i is argument i+1.
        shift = 1 if member(bv, func) and not (params and params[0].name == "this") else 0
        for at, p in enumerate(params):
            index = at + shift
            t = p.type
            if t.type_class != TypeClass.PointerTypeClass:
                continue
            target = t.target
            if target.type_class != TypeClass.NamedTypeReferenceClass:
                continue
            cls = by_name.get(str(target.name))
            if cls is not None:
                out[(faddr, index)] = (cls, "type", None)

    def root_class(faddr, root, offset):
        if root == ("this",):
            cls = claimed.get(faddr)
            if cls is not None and faddr in cls.thunks:
                return None
        elif root[0] in ("alloc", "stack"):
            cls = site_class.get((faddr, root))
        elif root[0] == "param":
            cls = out.get((faddr, root[1]), (None, None, None))[0]
        else:
            return None
        if cls is None:
            return None
        if offset:
            name = base_at(cls, offset, by_name)
            cls = by_name.get(name) if name else None
        return cls

    candidates = {}
    for faddr, ff in facts.items():
        for ap in ff.argpasses:
            # this of a method is its class; this of an implementation shared
            # by unrelated classes is nothing callers can settle.
            if ap.index == 0 and (ap.callee in claimed or ap.callee in unowned):
                continue
            cls = root_class(faddr, ap.root, ap.offset)
            if cls is not None:
                candidates.setdefault((ap.callee, ap.index), []).append(cls)
    for key, cands in candidates.items():
        for c in cands:
            if all(d is c or derives_from(d, c, by_name) for d in cands):
                if key in out:
                    out[key] = (out[key][0], out[key][1], c)
                else:
                    out[key] = (c, "argpass", None)
                break
    return out



def base_table_offset(derived, base, by_name):
    """Object offset of the vtable inside `derived` that serves the `base`
    sub-object. Non-virtual bases have static offsets; a virtual base's
    sub-object sits at a runtime offset, but derived's own table for it is
    the one secondary table no non-virtual base chain explains."""
    off = base_offset_in(derived, base, by_name)
    if off is not None:
        return off

    def explained(cls, at, depth=0):
        out = {at + o for o in cls.vtables}
        if depth > 32:
            return out
        for b in cls.bases:
            bc = by_name.get(b.name)
            if bc is not None and b.offset is not None:
                out |= explained(bc, at + b.offset, depth + 1)
        return out

    covered = set()
    for b in derived.bases:
        bc = by_name.get(b.name)
        if bc is not None and b.offset is not None:
            covered |= explained(bc, b.offset)
    virtual_bases = [b for b in derived.bases if b.virtual]
    candidates = [o for o in derived.vtables if o != 0 and o not in covered]
    if len(candidates) == 1 and len(virtual_bases) == 1 and virtual_bases[0].name == base.name:
        return candidates[0]
    return None
