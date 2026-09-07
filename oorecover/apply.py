"""Apply recovered class models to the Binary Ninja database.

Per class: a structure with embedded non-virtual bases, vptr slots and
observed members; a vtable structure of typed function pointers per table
(so HLIL renders this->vtable->method(...)); the vtable data variable and
symbol; renamed auto-named methods; and a typed this parameter on every
owned function. All changes land in one undo action. Types that exist and
were not created by a previous run are kept, never overwritten.
"""
import re
import time

from binaryninja import (FunctionParameter, QualifiedName, ReturnValue, StructureBuilder, Symbol,
                         Type, ValueLocation, ValueLocationComponent)
from binaryninja.enums import NamedTypeReferenceClass, SymbolType, TypeClass

from .model import topo_order, base_at
from .names import (META_TYPES, demangle, mangled, mangled_class, member, member_class,
                    msvc_static, split_qualified)

_META_KEY = META_TYPES
_NAMES_KEY = "oorecover.functions"


def qualified(name):
    """Qualified type name matching what Binary Ninja's demanglers produce
    for the same class, so demangled signatures resolve to our types."""
    return QualifiedName(split_qualified(name))


def vtable_type_name(cls, off, by_name):
    """Binary Ninja's own spelling, so its RTTI analysis' types are updated
    in place instead of duplicated: X::VTable for the primary table and
    Base::X::VTable for the table serving the Base sub-object at off."""
    if off == 0:
        return cls.name + "::VTable"
    base = base_at(cls, off, by_name)
    if base is not None:
        return "%s::%s::VTable" % (base, cls.name)
    return "%s::VTable_%x" % (cls.name, off)


def vtable_symbol_name(cls, off, by_name, abi):
    """Binary Ninja's symbol convention for tables its RTTI analysis missed."""
    name = "_vtable_for_" + cls.name if abi == "itanium" else cls.name + "::`vftable'"
    if off != 0:
        base = base_at(cls, off, by_name)
        name += "{for `%s'}" % base if base is not None else "{at %#x}" % off
    return name


def applied_vtable_name(bv, addr):
    """Name of the VTable struct on the data variable at addr, if any."""
    dv = bv.get_data_var_at(addr)
    if dv is None:
        return None
    try:
        t = dv.type
        if t.type_class == TypeClass.NamedTypeReferenceClass:
            name = str(t.name)
        elif t.registered_name is not None:
            name = str(t.registered_name.name)
        else:
            return None
    except Exception:
        return None
    return name if "::VTable" in name else None


def _assign_vtable_names(bv, order, by_name):
    """One struct name per table. A name already on the table (Binary
    Ninja's RTTI analysis, or our previous run) is kept so the type is
    updated in place; its analysis reuses one name for several tables of a
    class with virtual bases, so a name serves the first table that claims it."""
    names = {}
    claimed = set()
    for cls in order:
        for off in sorted(cls.vtables):
            existing = applied_vtable_name(bv, cls.vtables[off].address)
            if existing is not None and existing not in claimed:
                names[(cls.name, off)] = existing
                claimed.add(existing)
    for cls in order:
        for off in sorted(cls.vtables):
            if (cls.name, off) in names:
                continue
            name = vtable_type_name(cls, off, by_name)
            if name in claimed:
                name = "%s_%x" % (name, off)
            names[(cls.name, off)] = name
            claimed.add(name)
    return names


def _prune_vtable_types(bv, own, log=print):
    """Drop Binary Ninja's auto-defined VTable structs that nothing uses:
    the placeholders its RTTI analysis creates without ever applying them."""
    pruned = 0
    for name in list(bv.types.keys()):
        text = str(name)
        if not text.endswith("::VTable") or text in own:
            continue
        try:
            if not bv.is_type_auto_defined(name):
                continue
            if bv.get_type_refs_for_type(name, 1):
                continue
            if next(iter(bv.get_code_refs_for_type(name, 1)), None) is not None:
                continue
            if next(iter(bv.get_data_refs_for_type(name, 1)), None) is not None:
                continue
            bv.undefine_type(bv.get_type_id(name))
            pruned += 1
        except Exception as e:
            log("[oorecover] prune %s failed: %s" % (text, e))
    return pruned


def _slot_type(bv, func, void_ptr):
    """Pointer type for a vtable slot. A slot's static type must allow
    returning even when the function installed in it (MSVC's _purecall,
    a noreturn stub in abstract classes) does not, or every virtual call
    through the slot would truncate the caller's control flow."""
    if func is None:
        return void_ptr
    ftype = func.type
    try:
        if not ftype.can_return:
            b = ftype.mutable_copy()
            b.can_return = True
            ftype = b.immutable_copy()
    except Exception:
        pass
    return Type.pointer(bv.arch, ftype)


def _vtable_ptr(bv, name):
    ref = Type.named_type_reference(NamedTypeReferenceClass.StructNamedTypeClass, flat(name))
    return Type.pointer(bv.arch, ref)


def flat(name):
    """Single-component qualified name: what Binary Ninja's RTTI analysis
    uses for its VTable structs (unlike the demanglers, which split on ::)."""
    return QualifiedName([name])


def type_members(bv, name):
    """Applied structure members for the report: (width, [[offset, name, type]])."""
    t = bv.get_type_by_name(qualified(name))
    if t is None:
        t = bv.get_type_by_name(flat(name))
    if t is None:
        return None
    try:
        return {"width": t.width,
                "members": [[m.offset, m.name, str(m.type)] for m in t.members]}
    except Exception:
        return {"width": t.width, "members": None}


def _own_types(bv):
    return _own_metadata(bv, _META_KEY)


def _own_metadata(bv, key):
    try:
        val = bv.query_metadata(key)
    except Exception:
        return set()
    return set(val) if isinstance(val, (list, tuple)) else set()


def _own_functions(bv):
    return {int(v) for v in _own_metadata(bv, _NAMES_KEY)}


def _member_type(bv, size, hint):
    if hint == "ptr" and size == bv.address_size:
        return Type.pointer(bv.arch, Type.void())
    if size in (1, 2, 4, 8):
        return Type.int(size, False)
    return Type.array(Type.int(1, False), size)


def _auto_named(func, own_functions=frozenset()):
    """True for functions we may name: Binary Ninja's sub_ names and names a
    previous run of ours assigned (re-runs correct earlier attributions)."""
    sym = func.symbol
    return sym is None or sym.short_name.startswith("sub_") or func.start in own_functions


def _explicit_params(bv, func, cls_name):
    """The explicit parameter list encoded in a mangled name, when the name
    is a member of cls_name; None for globals and anything else."""
    if not mangled(func):
        return None
    try:
        demangled = demangle(bv, func.symbol.raw_name)
        if demangled is None:
            return None
        dtype, parts = demangled
        if dtype is None or dtype.type_class != TypeClass.FunctionTypeClass:
            return None
        if "::".join(parts[:-1]) != cls_name:
            return None
        params = list(dtype.parameters)
        if params and params[0].name == "this":
            params = params[1:]
        return params
    except Exception:
        return None


def _same_type(a, b):
    norm = lambda t: re.sub(r"\b(struct|class|enum|union|const)\s+", "", str(t)).replace(" ", "")
    return norm(a.type) == norm(b.type)


def _short(name):
    return name.split("::")[-1]


def _slot_label(func, index):
    if func is None or _auto_named(func):
        return "vfunc_%d" % index
    short = _short(func.symbol.short_name)
    if short.startswith("~"):
        return "dtor"
    short = re.sub(r"[^0-9A-Za-z_]", "_", short)
    return short or "vfunc_%d" % index


def _param0_struct(ftype):
    """Name of the struct the first parameter points to, if any."""
    try:
        params = list(ftype.parameters)
        if not params:
            return None
        p = params[0].type
        if p.type_class != TypeClass.PointerTypeClass:
            return None
        t = p.target
        if t.type_class == TypeClass.NamedTypeReferenceClass:
            return str(t.name)
    except Exception:
        return None
    return None


def _named_type(name):
    return Type.named_type_reference(NamedTypeReferenceClass.StructNamedTypeClass, qualified(name))


def _named_ptr(bv, name):
    return Type.pointer(bv.arch, _named_type(name))


def _return_value(ftype):
    """The function type's return value with its location: rebuilding a
    signature from the bare return type would reset a hidden-pointer return
    (or any custom location) to the calling convention's default."""
    return ReturnValue(ftype.return_value, ftype.return_value_location)


_STRUCT_REFS = (NamedTypeReferenceClass.StructNamedTypeClass, NamedTypeReferenceClass.ClassNamedTypeClass,
                NamedTypeReferenceClass.UnionNamedTypeClass)


def _is_indirect(ftype):
    """True when the type already returns through the hidden pointer."""
    loc = ftype.return_value_location
    return loc is not None and loc.location.indirect


def _default_locations(params):
    """The parameters with their locations left to the calling convention.
    Binary Ninja pins some demangled parameters to a register (an enum
    parameter reads `arg2 @ rsi` on x86-64) and reports every parameter of a
    signature it laid out as pinned. Those pins describe the layout without
    the hidden return pointer: once the return goes through it, this moves
    to the same register and Binary Ninja drops this and repeats the pinned
    parameter. Default locations let it lay them out after the buffer."""
    return [FunctionParameter(p.type, p.name) for p in params]


def _indirect_return(bv, func, ftype, name, size, own):
    """Return value of a method returning a struct by value through the
    calling convention's hidden pointer, so Binary Ninja lays this out in
    the next argument register and shows the buffer as the result. Binary
    Ninja's return type is kept when it already is a struct; otherwise a
    placeholder named after the method spans the writes into the buffer."""
    if _is_indirect(ftype):
        return ReturnValue(ftype.return_value, ftype.return_value_location)
    rtype = ftype.return_value
    is_struct = (rtype.type_class == TypeClass.StructureTypeClass
                 or (rtype.type_class == TypeClass.NamedTypeReferenceClass
                     and rtype.named_type_class in _STRUCT_REFS))
    if not is_struct:
        placeholder = name + "_result"
        if bv.get_type_by_name(qualified(placeholder)) is None or placeholder in own:
            sb = StructureBuilder.create()
            if size > 0:
                sb.width = size
            bv.define_user_type(qualified(placeholder), Type.structure_type(sb))
            own.add(placeholder)
        rtype = _named_type(placeholder)
    cc = ftype.calling_convention or func.calling_convention
    buf = cc.get_indirect_return_value_location()
    echo = cc.get_returned_indirect_return_value_pointer()
    location = ValueLocation([ValueLocationComponent(buf)], indirect=True, returned_pointer=echo)
    return ReturnValue(rtype, location)


class _Names:
    def __init__(self):
        self.used = set()

    def __call__(self, base):
        name = base
        n = 1
        while name in self.used:
            name = "%s_%d" % (base, n)
            n += 1
        self.used.add(name)
        return name


MAX_VCALL_TARGETS = 32


def apply_virtual_calls(bv, vcalls, log=print):
    """Add user cross-references from resolved virtual call sites to their
    implementations. Sites with more candidates than MAX_VCALL_TARGETS get
    only the static class's own slot, to keep xrefs useful."""
    refs = 0
    capped = 0
    for caller, insn, _cls_name, _exact, targets in vcalls:
        func = bv.get_function_at(caller)
        if func is None:
            continue
        chosen = targets
        if len(targets) > MAX_VCALL_TARGETS:
            chosen = targets[:1]
            capped += 1
        for target in chosen:
            try:
                func.add_user_code_ref(insn, target)
                refs += 1
            except Exception as e:
                log("[oorecover] xref %#x -> %#x failed: %s" % (insn, target, e))
    log("[oorecover] virtual calls: %d sites, %d xrefs added, %d sites capped"
        % (len(vcalls), refs, capped))
    return refs


def _declared_shift(bv, func):
    """Register-numbered argument index minus declared parameter index: 1 for
    a member function whose demangled signature omits the implicit this
    (Binary Ninja 5.3 and earlier; 6.0 declares it)."""
    try:
        params = list(func.type.parameters)
    except Exception:
        return 0
    if member(bv, func) and not (params and params[0].name == "this"):
        return 1
    return 0


def apply_namespace_functions(bv, log=print):
    """Binary Ninja 6.0 declares this on every Itanium function with a nested
    scope, namespace functions included, which shifts their real parameters
    one register to the right. A function whose scope has no class evidence
    gets exactly the explicit list its mangled name encodes."""
    repaired = 0
    for func in bv.functions:
        if not mangled(func) or not func.symbol.raw_name.startswith("_Z") or member(bv, func):
            continue
        try:
            ftype = func.type
            params = list(ftype.parameters)
            if not (params and params[0].name == "this"):
                continue
            demangled = demangle(bv, func.symbol.raw_name)
            if demangled is None or demangled[0] is None \
                    or demangled[0].type_class != TypeClass.FunctionTypeClass:
                continue
            explicit = list(demangled[0].parameters)
            if explicit and explicit[0].name == "this":
                explicit = explicit[1:]
            func.set_user_type(Type.function(
                _return_value(ftype), _default_locations(explicit),
                calling_convention=ftype.calling_convention,
                variable_arguments=ftype.has_variable_arguments))
            repaired += 1
        except Exception as e:
            log("[oorecover] namespace function %#x failed: %s" % (func.start, e))
    if repaired:
        log("[oorecover] removed the bogus this from %d namespace function signatures" % repaired)
    return repaired


def apply_member_this(bv, facts, class_names, claimed, log=print):
    """Insert the implicit this into demangled member signatures of recovered
    classes for functions no class owns (non-virtual methods), where the
    function reads the this register. Call sites then carry the object, so
    the next pass sees this-calls and argument passing to these functions."""
    inserted = 0
    for faddr, ff in facts.items():
        if not ff.entry_this or faddr in claimed:
            continue
        func = bv.get_function_at(faddr)
        if func is None or not mangled(func) or msvc_static(func):
            continue
        try:
            ftype = func.type
            params = list(ftype.parameters)
            if params and params[0].name == "this":
                continue
            cls_name = member_class(bv, func)
            if cls_name not in class_names:
                continue
            func.set_user_type(Type.function(
                _return_value(ftype), [FunctionParameter(_named_ptr(bv, cls_name), "this")] + params,
                calling_convention=ftype.calling_convention,
                variable_arguments=ftype.has_variable_arguments))
            inserted += 1
        except Exception as e:
            log("[oorecover] member this %#x failed: %s" % (faddr, e))
    if inserted:
        log("[oorecover] inserted this into %d non-virtual member signatures" % inserted)
    return inserted


def apply_unowned(bv, unowned, log=print):
    """An implementation shared by unrelated classes serves objects of all of
    them, so its this is a void pointer. Said explicitly, because Binary Ninja
    otherwise propagates whichever class's vtable slot type it meets first."""
    typed = 0
    for faddr in sorted(unowned):
        func = bv.get_function_at(faddr)
        if func is None:
            continue
        try:
            ftype = func.type
            params = list(ftype.parameters)
            this = FunctionParameter(Type.pointer(bv.arch, Type.void()), "this")
            if params and params[0].name == "this":
                if _param0_struct(ftype) is None:
                    continue
                params[0] = this
            elif mangled(func) and not msvc_static(func):
                params.insert(0, this)   # a pre-6.0 demangled member signature omits this
            else:
                continue
            func.set_user_type(Type.function(
                _return_value(ftype), params, calling_convention=ftype.calling_convention,
                variable_arguments=ftype.has_variable_arguments))
            typed += 1
        except Exception as e:
            log("[oorecover] shared this %#x failed: %s" % (faddr, e))
    if typed:
        log("[oorecover] %d shared implementations given a void this" % typed)


def apply_param_types(bv, param_classes, claimed, class_names, log=print):
    """Type parameters that callers only ever pass known-class objects to,
    on functions no class owns. Existing struct pointer types are kept. A
    member function whose signature lacks this gets it inserted, typed by
    its mangled class when recovered, else by the inferred class."""
    typed = 0
    by_func = {}
    for (faddr, index), name in param_classes.items():
        if faddr not in claimed:
            by_func.setdefault(faddr, []).append((index, name))
    for faddr, entries in by_func.items():
        func = bv.get_function_at(faddr)
        if func is None:
            continue
        try:
            ftype = func.type
            params = list(ftype.parameters)
            shift = _declared_shift(bv, func)
            changed = False
            for index, name in sorted(entries):
                if index == 0 and shift == 1:
                    cls_name = mangled_class(bv, func)
                    if cls_name not in class_names:
                        cls_name = name
                    params.insert(0, FunctionParameter(_named_ptr(bv, cls_name), "this"))
                    shift = 0
                    changed = True
                    continue
                at = index - shift
                if at < 0 or at >= len(params):
                    continue
                current = params[at].type
                if (current.type_class == TypeClass.PointerTypeClass
                        and current.target.type_class == TypeClass.NamedTypeReferenceClass):
                    continue
                params[at] = FunctionParameter(_named_ptr(bv, name), params[at].name)
                changed = True
            if not changed:
                continue
            func.set_user_type(Type.function(
                _return_value(ftype), params, calling_convention=ftype.calling_convention,
                variable_arguments=ftype.has_variable_arguments))
            typed += 1
        except Exception as e:
            log("[oorecover] param type %#x failed: %s" % (faddr, e))
    if typed:
        log("[oorecover] typed class pointer parameters on %d functions" % typed)
    return typed


def apply_instances(bv, instances, defined, log=print):
    """Type static objects with the class their constructor built there.
    A variable the user already gave a structure type keeps it."""
    typed = 0
    for addr, name in sorted(instances.items()):
        if name not in defined:
            continue
        try:
            var = bv.get_data_var_at(addr)
            if var is not None:
                t = var.type
                if t.type_class in (TypeClass.StructureTypeClass, TypeClass.NamedTypeReferenceClass):
                    continue
            bv.define_user_data_var(addr, _named_type(name))
            typed += 1
        except Exception as e:
            log("[oorecover] instance %#x failed: %s" % (addr, e))
    if typed:
        log("[oorecover] typed %d static instances" % typed)
    return typed


def apply_model(bv, classes, log=print, progress=None, vcalls=(), abi="itanium", param_classes=None,
                facts=None, unowned=(), instances=None):
    arch = bv.arch
    ptrsize = bv.address_size
    void_ptr = Type.pointer(arch, Type.void())
    own = _own_types(bv)
    own_functions = _own_functions(bv)
    by_name = {c.name: c for c in classes}
    order = topo_order(classes)
    defined = set()
    failures = 0
    newly_typed = 0
    repaired = 0
    kept = 0
    stale = {n for n in own
             if ("::vtbl" in n or n.endswith("::VTable"))
             and bv.get_type_by_name(qualified(n)) is not None
             and not bv.is_type_auto_defined(qualified(n))}

    table_names = _assign_vtable_names(bv, order, by_name)

    def vt_type_name(cls, off):
        return table_names[(cls.name, off)]

    t_start = time.time()
    undo = bv.begin_undo_actions()
    try:
        for n, cls in enumerate(order):
            if progress:
                progress("types %d/%d" % (n + 1, len(order)))
            existing = bv.get_type_by_name(qualified(cls.name))
            if existing is not None and cls.name not in own:
                log("[oorecover] %s: type exists, kept" % cls.name)
                defined.add(cls.name)
                continue
            sb = StructureBuilder.create()
            if cls.size > 0:
                sb.width = cls.size
            covered = []
            for b in cls.bases:
                if b.virtual or b.offset is None or b.name not in by_name:
                    continue
                bsize = by_name[b.name].size
                if bsize <= 0 or b.name not in defined:
                    continue
                sb.insert(b.offset, Type.named_type_from_registered_type(bv, qualified(b.name)),
                          "_base_" + re.sub(r"[^0-9A-Za-z_]", "_", _short(b.name)))
                covered.append((b.offset, b.offset + bsize))

            for off, name in sorted(cls.embedded.items()):
                esize = by_name[name].size if name in by_name else 0
                if esize <= 0 or name not in defined or any(s <= off < e for s, e in covered):
                    continue
                sb.insert(off, Type.named_type_from_registered_type(bv, qualified(name)),
                          "obj_%x" % off)
                covered.append((off, off + esize))

            def in_base(off):
                return any(s <= off < e for s, e in covered)

            for off in sorted(cls.vtables):
                if in_base(off):
                    continue
                sb.insert(off, _vtable_ptr(bv, vt_type_name(cls, off)),
                          "_vftable" if off == 0 else "_vftable_%x" % off)
            offsets = sorted(o for o in cls.members if not in_base(o) and o not in cls.vtables)
            bounds = sorted(list(cls.vtables) + [s for s, _e in covered])
            prev_end = 0
            for i, off in enumerate(offsets):
                if off < prev_end:
                    continue
                size, hint, _w, _r = cls.members[off]
                limit = offsets[i + 1] if i + 1 < len(offsets) else None
                for b in bounds:
                    if b > off and (limit is None or b < limit):
                        limit = b
                if limit is not None and off + size > limit:
                    size = limit - off
                    if size != ptrsize:
                        hint = "int"
                sb.insert(off, _member_type(bv, size, hint), "m_%x" % off)
                prev_end = off + size
            try:
                bv.define_user_type(qualified(cls.name), Type.structure_type(sb))
                own.add(cls.name)
                defined.add(cls.name)
            except Exception as e:
                failures += 1
                log("[oorecover] type %s failed: %s" % (cls.name, e))

        for cls in order:
            if cls.name not in defined:
                continue
            cls_ptr = _named_ptr(bv, cls.name)
            slot_index = {}
            for off in sorted(cls.vtables):
                for i, fn in enumerate(cls.vtables[off].slots):
                    if fn is not None:
                        slot_index.setdefault(fn, i)

            def base_ptr_at(off):
                for b in cls.bases:
                    if b.offset == off and b.name in defined:
                        return _named_ptr(bv, b.name)
                return cls_ptr

            jobs = []
            for i, fn in enumerate(sorted(cls.ctors)):
                jobs.append((fn, "ctor" if i == 0 else "ctor_%d" % i, cls_ptr))
            for i, fn in enumerate(sorted(cls.dtors)):
                jobs.append((fn, "dtor" if i == 0 else "dtor_%d" % i, cls_ptr))
            for fn in sorted(cls.methods):
                jobs.append((fn, "vfunc_%d" % slot_index.get(fn, 0), cls_ptr))
            for fn, off in sorted(cls.thunks.items()):
                jobs.append((fn, "thunk_%x_%d" % (off, slot_index.get(fn, 0)), base_ptr_at(off)))
            for fn, slot in sorted(cls.shared.items()):
                jobs.append((fn, "shared_vfunc_%d" % slot, cls_ptr))
            for fn, label, this_ptr in jobs:
                func = bv.get_function_at(fn)
                if func is None:
                    continue
                try:
                    if _auto_named(func, own_functions):
                        func.name = cls.name + "::" + label
                        own_functions.add(fn)
                    ftype = func.type
                    params = list(ftype.parameters)
                    sret = bool(facts) and fn in facts and facts[fn].sret
                    if params and params[0].name == "sret":
                        params = params[1:]     # marking of releases before the native return location
                    has_this = bool(params) and params[0].name == "this"
                    current = _param0_struct(Type.function(ftype.return_value, params)) if has_this else None
                    if current is not None and current not in own and current != cls.name:
                        continue
                    if has_this or (params and not mangled(func)):
                        rest = params[1:]
                        if sret and not has_this and not _is_indirect(ftype):
                            rest = rest[1:]     # an auto signature lists the hidden buffer before this
                    else:
                        rest = params
                    explicit = _explicit_params(bv, func, cls.name)
                    if explicit is not None and len(rest) < len(explicit):
                        # An earlier run replaced leading parameters with this.
                        # Restore from the mangled name only when what is stored
                        # is a truncation of it, so refined or foreign signatures
                        # (type libraries, user edits) are never overwritten.
                        tail = explicit[len(explicit) - len(rest):]
                        if all(_same_type(a, b) for a, b in zip(rest, tail)):
                            if repaired < 5:
                                log("[oorecover] repair %#x %s: %s -> %s" % (
                                    fn, func.symbol.raw_name, [str(p.type) for p in rest],
                                    [str(p.type) for p in explicit]))
                            rest = explicit
                            repaired += 1
                        else:
                            kept += 1
                            if kept <= 5:
                                log("[oorecover] %#x %s: stored %s is not a truncation of %s; kept" % (
                                    fn, func.symbol.raw_name, [str(p.type) for p in rest],
                                    [str(p.type) for p in explicit]))
                    if not has_this:
                        newly_typed += 1
                    lead = [FunctionParameter(this_ptr, "this")]
                    ret = _return_value(ftype)
                    if sret:
                        ret = _indirect_return(bv, func, ftype,
                                               cls.name + "::" + _slot_label(func, slot_index.get(fn, 0)),
                                               facts[fn].sret_size, own)
                        rest = _default_locations(rest)
                    new_type = Type.function(
                        ret, lead + rest,
                        calling_convention=ftype.calling_convention,
                        variable_arguments=ftype.has_variable_arguments)
                    func.set_user_type(new_type)
                except Exception as e:
                    failures += 1
                    log("[oorecover] method %#x failed: %s" % (fn, e))

        for cls in order:
            if cls.name not in defined:
                continue
            for off in sorted(cls.vtables):
                t = cls.vtables[off]
                names = _Names()
                vsb = StructureBuilder.create()
                for i, fn in enumerate(t.slots):
                    if fn is None:
                        vsb.append(void_ptr, names("pure_%d" % i))
                        continue
                    func = bv.get_function_at(fn)
                    mtype = _slot_type(bv, func, void_ptr)
                    vsb.append(mtype, names(_slot_label(func, i)))
                vt_name = vt_type_name(cls, off)
                try:
                    bv.define_user_type(flat(vt_name), Type.structure_type(vsb))
                    own.add(vt_name)
                except Exception as e:
                    failures += 1
                    log("[oorecover] vtable type %s failed: %s" % (vt_name, e))
                    continue
                sym_name = vtable_symbol_name(cls, off, by_name, abi)
                try:
                    bv.define_user_data_var(
                        t.address, Type.named_type_from_registered_type(bv, flat(vt_name)))
                    if bv.get_symbol_at(t.address) is None:
                        bv.define_user_symbol(Symbol(SymbolType.DataSymbol, t.address, sym_name))
                except Exception as e:
                    failures += 1
                    log("[oorecover] vtable var %s failed: %s" % (sym_name, e))
        for name in sorted(stale):
            try:
                bv.undefine_user_type(qualified(name))
                own.discard(name)
            except Exception as e:
                log("[oorecover] removing old type %s failed: %s" % (name, e))
        if vcalls:
            apply_virtual_calls(bv, vcalls, log)
        # unowned: one implementation serving unrelated classes; its symbol
        # names only one of them, so it gets no this from that name either.
        claimed = {fn for cls in order for fn in cls.owns()} | {fn for cls in order for fn in cls.thunks} \
            | {fn for cls in order for fn in cls.shared} | set(unowned)
        namespaces = apply_namespace_functions(bv, log)
        if facts:
            newly_typed += apply_member_this(bv, facts, set(by_name), claimed, log)
        apply_unowned(bv, unowned, log)
        if instances:
            apply_instances(bv, instances, defined, log)
        if param_classes:
            apply_param_types(bv, param_classes, claimed, set(by_name), log)
        bv.store_metadata(_META_KEY, sorted(own))
        bv.store_metadata(_NAMES_KEY, sorted(own_functions))
        t_apply = time.time()
        bv.update_analysis_and_wait()
        t_reanalysis = time.time()
        # Reference indexes update with analysis; prune only once they reflect our retyping.
        pruned = _prune_vtable_types(bv, own, log)
        if stale or pruned:
            log("[oorecover] vtable types: %d old ones of ours removed, %d unused native ones removed"
                % (len(stale), pruned))
    finally:
        bv.commit_undo_actions(undo)
    log("[oorecover] applied %d class types (%d failures, %d functions gained a this parameter, "
        "%d signatures repaired from mangled names, %d mismatches kept); apply %.1fs, reanalysis %.1fs"
        % (len(defined), failures, newly_typed, repaired, kept, t_apply - t_start, t_reanalysis - t_apply))
    return newly_typed + namespaces
