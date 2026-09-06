"""Vtable discovery: symbol candidates plus a chunked pointer-run scan."""
from .abi import detect_abi, iter_data_sections
from .itanium import Itanium
from .msvc import MSVC

CHUNK = 1 << 20


def make_abi(name, bv, mem, log):
    return (MSVC if name == "msvc" else Itanium)(bv, mem, log)


def _has_code_ref(bv, addr):
    for _ref in bv.get_code_refs(addr, max_items=1):
        return True
    return False


def _pointer_candidates(bv, mem, progress=None, cancelled=None):
    """Positions of pointer-aligned code pointers and data pointers in data
    sections: (code_positions, [(position, data_pointer_value)])."""
    p = mem.ptrsize
    code = []
    data_ptrs = []
    sections = list(iter_data_sections(bv, mem))
    for n, section in enumerate(sections):
        if cancelled and cancelled():
            break
        if progress:
            progress("scanning %s (%d/%d)" % (section.name, n + 1, len(sections)))
        addr = (section.start + p - 1) // p * p
        while addr < section.end:
            size = min(CHUNK, section.end - addr)
            data = bv.read(addr, size)
            if data:
                for i, val in enumerate(mem.unpack_ptrs(data)):
                    if val == 0:
                        continue
                    if mem.is_code(val):
                        code.append(addr + i * p)
                    elif mem.is_data(val):
                        data_ptrs.append((addr + i * p, val))
            addr += size
    return code, data_ptrs


def _scan_with(bv, mem, abi, log, progress=None, cancelled=None):
    p = mem.ptrsize
    found = {}
    sym_cands = list(abi.symbol_candidates())
    # A vtable ends where the next one's symbol starts. Without RTTI the
    # header of the next table is two zero words, which a null-tolerant slot
    # read would swallow.
    sym_addrs = sorted({sym for _ap, sym, _raw in sym_cands})
    sym_end = {sym: (sym_addrs[i + 1] if i + 1 < len(sym_addrs) else None)
               for i, sym in enumerate(sym_addrs)}
    code_cands, data_ptrs = _pointer_candidates(bv, mem, progress, cancelled)
    abi.prime(abi.typeinfo_addrs_of([ap for ap, _symbol, _raw in sym_cands] + code_cands))
    succeeded = set()
    failures = {}
    for ap, symbol, raw in sym_cands:
        if symbol in succeeded:
            continue
        if ap in found:
            succeeded.add(symbol)
            continue
        why = []
        info = abi.parse_vtable_at(ap, why, trusted=True, bound=sym_end[symbol])
        if info is None:
            failures.setdefault(symbol, "; ".join(why))
            continue
        found[ap] = info
        succeeded.add(symbol)
        if not info.has_rtti:
            info.sym_addr = symbol
            info.sym_name = abi.symbol_class(raw)
    for symbol, reason in sorted(failures.items()):
        if symbol not in succeeded:
            log("[oorecover]   vtable symbol %#x rejected: %s" % (symbol, reason))

    skip_until = 0
    for ap in sorted(set(code_cands)):
        if ap in found or ap < skip_until:
            continue
        info = abi.parse_vtable_at(ap)
        if info is not None:
            found[ap] = info
            skip_until = ap + len(info.slots) * p

    # Tables whose slots are all null or imported (abstract classes) never
    # start with a code pointer; find them by their RTTI header instead.
    for pos, val in data_ptrs:
        ap = pos + p
        if ap in found or not abi.is_rtti_header_ref(val):
            continue
        info = abi.parse_vtable_at(ap)
        if info is not None and info.has_rtti:
            found[ap] = info

    tables = []
    for ap in sorted(found):
        info = found[ap]
        info.referenced = info.has_rtti or _has_code_ref(bv, ap)
        tables.append(info)
    return tables


def scan_vtables(bv, mem, log=print, progress=None, cancelled=None):
    """Returns (abi, tables). Tables without RTTI are provisional: the model
    keeps them only when code stores their address into an object."""
    name = detect_abi(bv)
    abi = make_abi(name, bv, mem, log)
    tables = _scan_with(bv, mem, abi, log, progress, cancelled)
    if not any(t.has_rtti for t in tables):
        other_name = "itanium" if name == "msvc" else "msvc"
        other = make_abi(other_name, bv, mem, log)
        alt = _scan_with(bv, mem, other, log, progress, cancelled)
        if any(t.has_rtti for t in alt):
            log("[oorecover] %s produced no RTTI tables; using %s" % (name, other_name))
            abi, tables = other, alt
    with_rtti = sum(1 for t in tables if t.has_rtti)
    log("[oorecover] %s vtable scan: %d tables (%d with RTTI, %d referenced without RTTI)"
        % (abi.name, len(tables), with_rtti,
           sum(1 for t in tables if not t.has_rtti and t.referenced)))
    for t in tables[:60]:
        log("[oorecover]   table %#x offset %d slots %d unresolved %d %s"
            % (t.address, t.object_offset, len(t.slots), len(t.unresolved),
               t.rtti_name or ("referenced" if t.referenced else "provisional")))
    return abi, tables
