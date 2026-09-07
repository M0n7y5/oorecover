"""OORecover: C++ class recovery on top of Binary Ninja analysis."""
import os
import time

import importlib

from . import validate
# The entry point's reload list predates this module; until Binary Ninja
# restarts it is refreshed here, after model (which calls through the module).
importlib.reload(validate)

from .abi import Memory
from .apply import apply_model
from .collect import collect_all
from .model import build_model
from .report import vtable_snapshot
from .scan import scan_vtables


class Result:
    __slots__ = ("abi", "tables", "facts", "classes", "functions_added", "vcalls", "native",
                 "param_classes", "earlier_vcalls", "findings", "unowned", "instances", "result_types",
                 "sret_hints")

    def __init__(self, abi, tables, facts, classes, functions_added, vcalls=(), native=None,
                 param_classes=None, notes=None):
        self.abi = abi
        self.tables = tables
        self.facts = facts
        self.classes = classes
        self.functions_added = functions_added
        self.vcalls = list(vcalls)
        self.native = native or {}
        self.param_classes = param_classes or {}   # (function, index) -> class name
        self.earlier_vcalls = []                    # resolved sites of previous passes
        notes = notes or {}
        self.findings = list(notes.get("findings", ()))   # contradictions withdrawn by validation
        self.unowned = dict(notes.get("unowned", {}))     # shared implementation -> its unrelated classes
        self.instances = dict(notes.get("instances", {}))  # static object address -> class name
        self.result_types = dict(notes.get("result_types", {}))  # method -> class of the struct it returns
        self.sret_hints = set(notes.get("sret_hints", ()))   # slot mates of struct returns, collected as such next


def trace_functions(bv, starts, log=print, callers=False):
    """Collect facts for the given functions only, with the collector's
    per-function trace, and log them. No model, no apply. With callers, the
    functions calling each listed one are traced too."""
    from .collect import collect_function, _make_name_check
    mem = Memory(bv)
    abi, tables = scan_vtables(bv, mem, log)
    vtable_addrs = {t.address for t in tables}
    is_alloc = _make_name_check(bv, abi.allocators, "operator new")
    is_dealloc = _make_name_check(bv, abi.deallocators, "operator delete")
    if callers:
        extra = []
        for start in starts:
            for ref in bv.get_code_refs(start):
                if ref.function is not None and ref.function.start not in extra:
                    extra.append(ref.function.start)
        log("[trace] callers: %s" % ", ".join("%#x" % a for a in extra))
        starts = list(starts) + extra
    for start in starts:
        func = bv.get_function_at(start)
        if func is None:
            log("[trace] %#x: no function" % start)
            continue
        log("[trace] %#x %s: %s" % (start, func.name, func.type))
        ff = collect_function(bv, mem, func, vtable_addrs, is_alloc, is_dealloc, log,
                              frozenset(fn for t in tables for fn in t.functions))
        if ff is None:
            log("[trace] no IL")
            continue
        log("[trace] vcalls %s" % [(hex(v.insn), v.root, v.object_offset, v.slot) for v in ff.vcalls])
        log("[trace] calls %s" % [(hex(c.insn), hex(c.callee), c.root, c.offset) for c in ff.calls][:12])
        log("[trace] accesses %d installs %d argpasses %d entry_this %s member_of %s sret %s" % (
            len(ff.accesses), len(ff.installs), len(ff.argpasses), ff.entry_this, ff.member_of, ff.sret))
        log("[trace] this accesses %s" % sorted({(a.offset, a.size, a.is_write) for a in ff.accesses if a.root == ("this",)}))
        log("[trace] allocs %s installs %s" % (
            [(hex(a.insn), a.size, hex(a.callee)) for a in ff.allocs],
            [(hex(i.insn), hex(i.vtable), i.root, i.offset) for i in ff.installs][:8]))


def run(bv, log=print, progress=None, cancelled=None, extra_functions=(), class_names=(),
        reuse=None, changed=(), changed_types=(), sret_hints=()):
    cancelled = cancelled or (lambda: False)
    if progress:
        progress("waiting for analysis")
    t0 = time.time()
    bv.update_analysis_and_wait()
    mem = Memory(bv)
    t1 = time.time()
    abi, tables = scan_vtables(bv, mem, log, progress, cancelled)
    if cancelled():
        return None
    added = 0
    for t in tables:
        if not t.referenced:
            continue
        for addr in t.unresolved:
            if bv.get_function_at(addr) is None and bv.add_function(addr) is not None:
                added += 1
    if added:
        log("[oorecover] created %d functions for vtable slots" % added)
        bv.update_analysis_and_wait()
        mem = Memory(bv)
    t2 = time.time()
    facts = collect_all(bv, mem, abi, tables, log, progress, cancelled, extra_functions,
                        class_names, reuse, changed, changed_types, sret_hints)
    if cancelled():
        return None
    t3 = time.time()
    classes, vcalls, param_classes, notes = build_model(bv, mem, tables, facts, log)
    native = vtable_snapshot(bv, tables)
    log("[oorecover] native rtti: %d VTable types, %d/%d tables with symbols, %d/%d typed"
        % (len(native["vtable_types"]),
           sum(1 for v in native["tables"].values() if v["symbol"]), len(tables),
           sum(1 for v in native["tables"].values() if v["type"]), len(tables)))
    t4 = time.time()
    log("[oorecover] timing: analysis wait %.1fs, scan %.1fs, collect %.1fs, model %.1fs"
        % (t1 - t0, t2 - t1, t3 - t2, t4 - t3))
    return Result(abi.name, tables, facts, classes, added, vcalls, native, param_classes, notes)


_TESTS = os.path.join(os.path.dirname(os.path.dirname(os.path.abspath(__file__))), "tests")
_TRACE_FILE = os.path.join(_TESTS, "trace.txt")
_REANALYZE_FILE = os.path.join(_TESTS, "reanalyze.txt")


def run_and_apply(bv, log=print, progress=None, cancelled=None):
    """Recover and apply. Functions whose signatures hid the this parameter
    (demangled void() types, unanalysed callees) get one in the first pass;
    call sites then carry arguments, so a second pass sees the calls."""
    if os.path.isfile(_REANALYZE_FILE):
        # Measuring what a core upgrade changes: throw away the analysis the
        # database was saved with and rebuild it before recovering.
        t0 = time.time()
        log("[oorecover] reanalysing the whole binary first")
        bv.reanalyze()
        bv.update_analysis_and_wait()
        log("[oorecover] reanalysis took %.0fs" % (time.time() - t0))
    if os.path.isfile(_TRACE_FILE):
        with open(_TRACE_FILE) as f:
            words = f.read().split()
        starts = [int(x, 0) for x in words if x.startswith("0x")]
        if "after-apply" in words:
            first = run(bv, log, progress, cancelled)
            if first is not None and first.classes:
                apply_model(bv, first.classes, log, progress, first.vcalls, first.abi,
                            first.param_classes, first.facts, first.unowned, first.instances,
                            result_types=first.result_types)
        trace_functions(bv, starts, log, callers="callers" in words)
        return Result("trace", [], {}, [], 0)
    result = None
    extra = set()
    class_names = set()
    earlier = []
    reuse = None
    retyped = set()
    retyped_types = set()
    sret_hints = set()
    for n in range(2):
        result = run(bv, log, progress, cancelled, extra, class_names, reuse, retyped, retyped_types,
                     sret_hints)
        if result is None:
            log("[oorecover] cancelled")
            return None
        result.earlier_vcalls = earlier
        earlier = earlier + [result.vcalls]
        if not result.classes:
            log("[oorecover] no classes found")
            return result
        retyped = set()
        retyped_types = set()
        newly_typed = apply_model(bv, result.classes, log, progress, result.vcalls, result.abi,
                                  result.param_classes, result.facts, result.unowned,
                                  result.instances, retyped, retyped_types, result.result_types)
        if len(result.tables) <= 16:
            final = vtable_snapshot(bv, result.tables)
            for addr, info in sorted(final["tables"].items()):
                log("[oorecover]   final %s: %s | %s" % (addr, info["symbol"], info["type"]))
            log("[oorecover]   final VTable types: %s" % final["vtable_types"])
        class_names = {c.name for c in result.classes}
        before = len(extra)
        for cls in result.classes:
            for ctor in cls.ctors:
                for ref in bv.get_code_refs(ctor):
                    if ref.function is not None:
                        extra.add(ref.function.start)
        for (faddr, _index) in result.param_classes:
            if faddr not in result.facts:
                extra.add(faddr)
        sret_hints |= result.sret_hints
        if newly_typed == 0 and len(extra) == before and not result.sret_hints:
            break
        if n == 1:
            log("[oorecover] pass 2 done; %d functions discovered late, not visited" % (len(extra) - before))
            break
        reuse = result.facts
        log("[oorecover] pass %d retyped %d parameterless functions, %d signatures and %d types changed, "
            "%d new functions to visit; rerunning on the changed functions and their callers, "
            "reusing the other facts" % (n + 1, newly_typed, len(retyped), len(retyped_types),
                                         len(extra) - before))
    return result
