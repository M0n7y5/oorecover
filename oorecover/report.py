"""JSON report of a pipeline result, used by the test harness."""
from .apply import applied_vtable_name, type_members


def vtable_snapshot(bv, tables):
    """Symbols, data variable types and VTable struct names on the vtables."""
    per_table = {}
    for t in tables:
        sym = bv.get_symbol_at(t.address)
        dv = bv.get_data_var_at(t.address)
        per_table["%#x" % t.address] = {
            "symbol": sym.name if sym is not None else None,
            "type": str(dv.type) if dv is not None else None,
        }
    vt_types = sorted(str(n) for n in bv.types.keys() if str(n).endswith("::VTable"))
    return {"vtable_types": vt_types, "tables": per_table}


def return_location(func):
    """Return location text, e.g. *rdi -> *rax for a struct returned by
    value; None for the calling convention's default."""
    loc = func.return_value_location
    return None if loc is None else loc.location.to_string(func.arch)


def build_report(bv, result):
    classes = []
    for c in result.classes:
        funcs = {}
        for fn in sorted(c.methods | c.ctors | c.dtors | c.nonvirtual | set(c.thunks) | set(c.shared)):
            f = bv.get_function_at(fn)
            if f is not None:
                funcs["%#x" % fn] = {"name": f.name, "type": str(f.type),
                                     "return_location": return_location(f)}
        classes.append({
            "name": c.name,
            "has_rtti": c.has_rtti,
            "bases": [{"name": b.name, "offset": b.offset, "virtual": b.virtual}
                      for b in c.bases],
            "vtables": {str(off): {"address": "%#x" % t.address,
                                   "slots": [None if s is None else "%#x" % s
                                             for s in t.slots]}
                        for off, t in sorted(c.vtables.items())},
            "methods": ["%#x" % fn for fn in sorted(c.methods)],
            "nonvirtual": ["%#x" % fn for fn in sorted(c.nonvirtual)],
            "ctors": ["%#x" % fn for fn in sorted(c.ctors)],
            "dtors": ["%#x" % fn for fn in sorted(c.dtors)],
            "thunks": {"%#x" % fn: off for fn, off in sorted(c.thunks.items())},
            "shared": {"%#x" % fn: slot for fn, slot in sorted(c.shared.items())},
            "embedded": {str(off): name for off, name in sorted(c.embedded.items())},
            "construction_vtables": {derived: {str(off): "%#x" % t.address for off, t in sorted(tabs.items())}
                                     for derived, tabs in sorted(c.construction.items())},
            "members": {str(off): list(m) + ([c.member_classes[off]] if off in c.member_classes else [])
                        for off, m in sorted(c.members.items())},
            "size": c.size,
            "sites": c.sites,
            "site_functions": ["%#x %s" % (fn, root[0]) for fn, root in c.site_functions],
            "type": type_members(bv, c.name),
            "vtbl_types": {str(off): type_members(bv, applied_vtable_name(bv, t.address) or "")
                           for off, t in sorted(c.vtables.items())},
            "functions": funcs,
        })
    final_sites = {(caller, insn) for caller, insn, _c, _e, _t in result.vcalls}
    lost = []
    for n, earlier in enumerate(result.earlier_vcalls):
        for caller, insn, cls_name, exact, targets in earlier:
            if (caller, insn) not in final_sites:
                f = bv.get_function_at(caller)
                ff = result.facts.get(caller)
                now = None
                if ff is None:
                    now = "not collected"
                else:
                    match = [v for v in ff.vcalls if v.insn == insn]
                    now = ("root %s+%d slot %d" % (match[0].root, match[0].object_offset, match[0].slot)
                           if match else "no vcall fact")
                il = []
                try:
                    ssa = f.mlil.ssa_form
                    for bb in ssa.basic_blocks:
                        block = list(bb)
                        hit = [k for k, i in enumerate(block) if i.address == insn]
                        if hit:
                            il = ["%s: %s" % (i.operation.name, i) for i in block[max(0, hit[0] - 2):hit[0] + 1]]
                            seen = set()
                            todo = list(block[hit[0]].vars_read)
                            for _ in range(12):
                                if not todo:
                                    break
                                sv = todo.pop(0)
                                if sv in seen:
                                    continue
                                seen.add(sv)
                                d = ssa.get_ssa_var_definition(sv)
                                il.append("  def %s = %s" % (sv, "%s: %s" % (d.operation.name, d) if d is not None else "<param/undefined>"))
                                if d is not None:
                                    todo.extend(d.vars_read)
                            break
                except Exception:
                    pass
                lost.append({"pass": n + 1, "caller": "%#x" % caller,
                             "caller_name": f.name if f else None, "insn": "%#x" % insn,
                             "class": cls_name, "targets": len(targets), "now": now, "il": il})
    vcalls = []
    for caller, insn, cls_name, exact, targets in result.vcalls:
        f = bv.get_function_at(caller)
        vcalls.append({
            "caller": "%#x" % caller,
            "caller_name": f.name if f is not None else None,
            "caller_type": str(f.type) if f is not None else None,
            "insn": "%#x" % insn,
            "class": cls_name,
            "exact": exact,
            "targets": ["%#x" % t for t in targets],
            "target_names": [getattr(bv.get_function_at(t), "name", None) for t in targets],
        })
    return {
        "binary": bv.file.filename,
        "abi": result.abi,
        "ptrsize": bv.address_size,
        "tables": len(result.tables),
        "functions_added": result.functions_added,
        "classes": classes,
        "vcalls": vcalls,
        "lost_vcalls": lost,
        "findings": [{"kind": k, "class": c, "detail": d} for k, c, d in result.findings],
        "instances": {"%#x" % addr: {"class": name,
                                     "type": str(getattr(bv.get_data_var_at(addr), "type", None))}
                      for addr, name in sorted(result.instances.items())},
        "unowned": {"%#x" % fn: {"name": f.name, "type": str(f.type),
                                 "user": bool(getattr(f, "has_user_type", False))}
                    for fn in sorted(result.unowned)
                    for f in [bv.get_function_at(fn)] if f is not None},
        "native": result.native,
        "param_classes": {"%#x:%d" % (fn, idx): name
                          for (fn, idx), name in sorted(result.param_classes.items())},
        "final": vtable_snapshot(bv, result.tables),
    }
