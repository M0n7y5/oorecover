"""Mangled and qualified name helpers shared by the collector and the applier."""
from binaryninja.enums import TypeClass


_CONFIG = (None, None)


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


_MSVC_STATIC = "CDKLST"


def msvc_static(func):
    """True for MSVC-mangled static member functions (access code after the
    qualified name is one of the static variants)."""
    raw = func.symbol.raw_name if func.symbol is not None else ""
    if not raw.startswith("?"):
        return False
    end = raw.find("@@")
    return end > 0 and end + 2 < len(raw) and raw[end + 2] in _MSVC_STATIC
