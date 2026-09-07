"""Mangled and qualified name helpers shared by the collector and the applier."""
import re
import time

from binaryninja.enums import TypeClass, VariableSourceType
from binaryninja.types import QualifiedName


_CONFIG = (None, None)
_SCOPES = (None, {}, frozenset())
_ARITY = (None, {})   # per view: function start -> reads one argument register past its explicit list
META_TYPES = "oorecover.types"    # metadata key listing the types a run of ours defined
_REGISTER = VariableSourceType.RegisterVariableSourceType
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


def hidden_this(func):
    """True when the function reads the integer argument register after
    the ones its declared explicit parameters occupy: a member whose this
    the signature omits (5.3), or a 6.0 signature whose bogus this pushed
    the explicit list one register right so the function reads one fewer.
    None when the layout is not plain registers or no register follows."""
    cc = func.calling_convention
    if cc is None:
        return None
    regs = [func.arch.get_reg_index(r) for r in cc.int_arg_regs]
    pvars = list(func.parameter_vars)
    locs = func.parameter_locations.locations   # len() of the wrapper is broken in 6.0.10601
    used = set()
    for i, v in enumerate(pvars):
        if v.name == "this":
            continue
        var = locs[i].components[0].var if i < len(locs) and locs[i].components else v
        if var.source_type != _REGISTER or var.storage not in regs:
            return None
        used.add(var.storage)
    k = len(used)
    if k >= len(regs):
        return None
    mlil = func.mlil
    ssa = mlil.ssa_form if mlil is not None else None
    if ssa is None:
        return None
    for sv in ssa.ssa_vars:
        v = sv.var
        if (v.source_type == _REGISTER and v.storage == regs[k]
                and ssa.get_ssa_var_definition(sv) is None and ssa.get_ssa_var_uses(sv)):
            return True
    return False


def demangler_config(bv):
    """One demangler configuration per view. Asking a name for its own
    configuration is far too slow for the tens of thousands a pass demangles.
    Built directly from the view (whose platform is already cached, unlike
    the one `for_binary_view` wraps, which logs a deprecation warning).
    Template simplification follows the view's setting, so class names are
    spelled the way Binary Ninja spells its own symbols and types."""
    global _CONFIG
    cached, config = _CONFIG
    if cached is not bv:
        from binaryninja import Settings
        from binaryninja.demangle import DemanglerConfig
        simplify = bool(Settings().get_bool("analysis.types.templateSimplifier", bv))
        config = DemanglerConfig(None, bv, simplify)
        _CONFIG = (bv, config)
    return config


def demangle(bv, raw, flavour=None):
    """(type, name parts) for a mangled name, or None. flavour forces the
    demangler for names only one of them understands."""
    from binaryninja import demangle as api
    config = demangler_config(bv)
    if flavour == "gnu3":
        result = api.demangle_gnu3(config, raw)
    elif flavour == "msvc":
        result = api.demangle_ms(config, raw)
    else:
        result = api.demangle_any(raw, config)
    if result is None:
        return None
    return result.type, list(result.name.name)


def split_qualified(name):
    """Split 'a::b<c::d>::e' into ['a', 'b<c::d>', 'e']."""
    parts, depth, cur = [], 0, ""
    i = 0
    while i < len(name):
        ch = name[i]
        if ch == "<":
            depth += 1
        elif ch == ">":
            depth -= 1
        if depth == 0 and name.startswith("::", i):
            parts.append(cur)
            cur = ""
            i += 2
            continue
        cur += ch
        i += 1
    parts.append(cur)
    return [p for p in parts if p] or [name]


def mangled(func):
    """Functions typed from a demangled symbol. Binary Ninja 6.0 declares the
    implicit this of Itanium members (as MSVC always did); 5.3 databases and
    thunk symbols list only the explicit parameters, so callers check for a
    parameter named this before inserting one."""
    sym = func.symbol
    return sym is not None and sym.raw_name.startswith(("_Z", "?"))


def mangled_class(bv, func):
    """Qualified class of a mangled member function name, or None."""
    if not mangled(func):
        return None
    try:
        demangled = demangle(bv, func.symbol.raw_name)
        if demangled is None:
            return None
        dtype, parts = demangled
        if dtype is None or dtype.type_class != TypeClass.FunctionTypeClass:
            return None
        return "::".join(parts[:-1]) or None
    except Exception:
        return None


def _type_names(t, out, depth=0):
    """Names of the structures a type mentions, through pointers, references,
    arrays and function types."""
    if t is None or depth > 8:
        return
    if t.type_class == TypeClass.NamedTypeReferenceClass:
        out.add(str(t.name))
        return
    for child in t.children:
        _type_names(child, out, depth + 1)


def scan_scopes(bv, class_names=(), log=print):
    """Which Itanium scopes are classes. Binary Ninja 6.0 declares a this
    parameter for every function with a nested scope, and 5.3 databases leave
    the first argument register to be taken for one, so the name alone does
    not tell a namespace from a class. A scope is a class when the pipeline
    has evidence: a vtable or recovered class of that name, a constructor,
    destructor or cv-qualified member symbol (only members carry const), a
    demangled signature mentioning it as a parameter or return type (a
    namespace never is), or a structure type in the view that no run of ours
    created. A scope with none of that, and not the prefix of another scope
    (a namespace nesting classes; a struct returned by value reads one
    register more, which would pass for a hidden this), is a class when one
    of its functions reads the argument register past its explicit list
    (hidden_this). Cached per view; returns ({function start: scope},
    classes, functions whose scope flipped since the previous scan)."""
    global _SCOPES, _ARITY
    t0 = time.time()
    by_start = {}
    scopes = set()
    classes = set(class_names)
    mentioned = set()
    for func in bv.functions:
        sym = func.symbol
        if sym is None or not sym.raw_name.startswith("_Z"):
            continue
        raw = sym.raw_name
        scope = None
        try:
            demangled = demangle(bv, raw)
            if demangled is not None and demangled[0] is not None \
                    and demangled[0].type_class == TypeClass.FunctionTypeClass:
                dtype, parts = demangled
                scope = "::".join(parts[:-1]) or None
                if scope is not None:
                    last, prev = parts[-1], parts[-2].split("<")[0]
                    qualified = raw.startswith("_ZN") and raw[3] in "KVrRO"
                    if last == prev or last.startswith("~") or qualified:
                        classes.add(scope)
                _type_names(dtype.return_value, mentioned)
                for p in dtype.parameters:
                    if p.name != "this":
                        _type_names(p.type, mentioned)
        except Exception:
            pass
        by_start[func.start] = scope
        if scope is not None:
            scopes.add(scope)
    try:
        own = bv.query_metadata(META_TYPES)
    except Exception:
        own = []
    own = set(own) if isinstance(own, (list, tuple)) else set()
    for scope in scopes - classes:
        if scope in mentioned:
            classes.add(scope)
            continue
        if scope in own:
            continue
        t = bv.get_type_by_name(QualifiedName(split_qualified(scope)))
        if t is not None and t.type_class == TypeClass.StructureTypeClass and t.width > 0:
            classes.add(scope)
    cached_arity, arity = _ARITY
    if cached_arity is not bv:
        arity = {}
    t_arity = time.time()
    checked = 0
    prefixes = set()
    for scope in scopes:
        parts = split_qualified(scope)
        for n in range(1, len(parts)):
            prefixes.add("::".join(parts[:n]))
    for start, scope in by_start.items():
        if scope is None or scope in classes or scope in prefixes:
            continue
        if start not in arity:
            checked += 1
            try:
                arity[start] = hidden_this(bv.get_function_at(start))
            except Exception:
                arity[start] = None
        if arity[start]:
            classes.add(scope)
    _ARITY = (bv, arity)
    if checked:
        log("[oorecover] arity evidence: %d functions of scopes without other evidence read, %.1fs"
            % (checked, time.time() - t_arity))
    classes = frozenset(classes)
    cached, _old_starts, old = _SCOPES
    flipped = set()
    if cached is bv:
        flipped = {start for start, scope in by_start.items()
                   if scope is not None and (scope in classes) != (scope in old)}
    _SCOPES = (bv, by_start, classes)
    members = sum(1 for s in by_start.values() if s in classes)
    nested = sum(1 for s in by_start.values() if s is not None)
    log("[oorecover] %d functions are class members by name, %d are in namespaces "
        "(%d of %d scopes have class evidence, %.1fs)"
        % (members, nested - members, len(scopes & classes), len(scopes), time.time() - t0))
    return by_start, classes, flipped


def member_class(bv, func):
    """Qualified class of a mangled member function, or None. The MSVC
    mangling encodes membership, so the name decides; an Itanium scope counts
    only with class evidence (scan_scopes)."""
    if not mangled(func):
        return None
    if func.symbol.raw_name.startswith("?"):
        return mangled_class(bv, func)
    cached, by_start, classes = _SCOPES
    if cached is not bv:
        by_start, classes, _flipped = scan_scopes(bv)
    scope = by_start[func.start] if func.start in by_start else mangled_class(bv, func)
    return scope if scope in classes else None


def member(bv, func):
    """True when the mangled name places the function in a class, so its
    signature carries the implicit this (6.0) or omits it (5.3)."""
    return member_class(bv, func) is not None


_MSVC_STATIC = "CDKLST"


def msvc_static(func):
    """True for MSVC-mangled static member functions (access code after the
    qualified name is one of the static variants)."""
    raw = func.symbol.raw_name if func.symbol is not None else ""
    if not raw.startswith("?"):
        return False
    end = raw.find("@@")
    return end > 0 and end + 2 < len(raw) and raw[end + 2] in _MSVC_STATIC
