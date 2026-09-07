"""MLIL SSA fact collection.

Per function: an alias map from SSA variables to (root, offset) pairs, seeded
from the first parameter, allocation results, stack-object addresses and the
destinations of vtable stores, then propagated through copies, constant
displacements and phis. Against that map the pass records vtable installs,
member accesses, this-calls and allocations.
"""
import os
import time
import traceback

from binaryninja import MediumLevelILInstruction
from binaryninja import MediumLevelILOperation as Op
from binaryninja.enums import RegisterValueType, SymbolType, TypeClass, VariableSourceType

from .facts import AllocCall, ArgPass, MemberAccess, ThisCall, VirtualCall, VtableInstall
from .names import mangled, member, member_class, scan_scopes

MAX_PASSES = 64
MAX_ALLOC = 1 << 24
MAX_THUNK_INSNS = 8
_STACK = VariableSourceType.StackVariableSourceType
_REGISTER = VariableSourceType.RegisterVariableSourceType
_CONST_VALUES = (RegisterValueType.ConstantValue, RegisterValueType.ConstantPointerValue)
_CONSTS = (Op.MLIL_CONST, Op.MLIL_CONST_PTR, Op.MLIL_EXTERN_PTR)
_SETS = (Op.MLIL_SET_VAR_SSA, Op.MLIL_SET_VAR_ALIASED)
_FIELD_SETS = (Op.MLIL_SET_VAR_SSA_FIELD, Op.MLIL_SET_VAR_ALIASED_FIELD)
_FIELD_VARS = (Op.MLIL_VAR_SSA_FIELD, Op.MLIL_VAR_ALIASED_FIELD)
_CALLS = (Op.MLIL_CALL_SSA, Op.MLIL_TAILCALL_SSA)
_VCALL_SITES = _CALLS + (Op.MLIL_JUMP,)
_LOADS = (Op.MLIL_LOAD_SSA, Op.MLIL_LOAD_STRUCT_SSA)
_STORES = (Op.MLIL_STORE_SSA, Op.MLIL_STORE_STRUCT_SSA)


class FunctionFacts:
    __slots__ = ("address", "installs", "accesses", "calls", "allocs", "stack_accesses",
                 "tail_target", "vcalls", "reach", "argpasses", "entry_this", "member_of",
                 "sret", "sret_size")

    def __init__(self, address):
        self.address = address
        self.installs = []        # VtableInstall
        self.accesses = []        # MemberAccess
        self.calls = []           # ThisCall
        self.allocs = []          # AllocCall
        self.stack_accesses = []  # (insn, storage, size, is_write)
        self.tail_target = None   # jump target when the function is a thunk
        self.vcalls = []          # VirtualCall
        self.reach = 0            # largest this+K address the function forms
        self.argpasses = []       # ArgPass
        self.entry_this = False   # reads its incoming this (declared or by register)
        self.member_of = None     # class the mangled symbol places it in, if any (names.member_class)
        self.sret = False         # returns a struct by value: this follows the hidden buffer
        self.sret_size = 0        # extent of the writes into that buffer

    def empty(self):
        return not (self.installs or self.accesses or self.calls or self.allocs
                    or self.tail_target or self.vcalls or self.argpasses or self.entry_this)


def _key(sv):
    return (sv.var.identifier, sv.version)


def _const(expr):
    """Constant value of an expression, using dataflow for non-literal forms."""
    if expr.operation in _CONSTS:
        return expr.constant
    try:
        value = expr.value
    except Exception:
        return None
    if value.type in _CONST_VALUES:
        return value.value
    return None


def _param_storage(func, index):
    """(source type, storage) of declared parameter index, from its location:
    a struct returned by value moves this past the hidden buffer pointer,
    and the location is what Binary Ninja lays the parameters out with."""
    locs = func.parameter_locations.locations   # len() of the wrapper is broken in 6.0.10601
    if index < len(locs) and locs[index].components:
        var = locs[index].components[0].var
        return (var.source_type, var.storage)
    pvars = list(func.parameter_vars)
    if index < len(pvars):
        return (pvars[index].source_type, pvars[index].storage)
    return None


def _arg_storage(func, at):
    """(source type, storage) of integer argument at of the calling
    convention: a register, else the stack slot past the return address."""
    cc = func.calling_convention
    regs = list(cc.int_arg_regs) if cc is not None else []
    if len(regs) > at:
        return (_REGISTER, func.arch.get_reg_index(regs[at]))
    return (_STACK, func.arch.address_size * (at - len(regs) + 1))


def _storage_after_return_buffer(func):
    """(source type, storage) of the argument following the calling
    convention's hidden return buffer pointer: where this lives when the
    function returns a struct by value."""
    cc = func.calling_convention
    if cc is None:
        return _arg_storage(func, 1)
    buf = cc.get_indirect_return_value_location()
    if buf.source_type == _REGISTER:
        indices = [func.arch.get_reg_index(r) for r in cc.int_arg_regs]
        if buf.storage in indices:
            return _arg_storage(func, indices.index(buf.storage) + 1)
        return _arg_storage(func, 1)
    return (_STACK, buf.storage + func.arch.address_size)


def _returns_indirect(func):
    """True when the signature already returns through a hidden pointer."""
    loc = func.return_value_location
    return loc is not None and loc.location.indirect


def _this_keys(bv, func, ssa, sret=False):
    """SSA keys of the incoming this-pointer: the parameter named this when
    the function type declares one, else the first parameter when the type
    has one, else the first integer argument register (or the first stack
    argument) of the calling convention. Demangled names give constructors
    a void() type that hides the implicit this. With sret the declared
    signature is wrong about a struct returned by value: this is the
    argument after the hidden return buffer."""
    pvars = list(func.parameter_vars)
    storage = None
    if sret:
        storage = _storage_after_return_buffer(func)
    else:
        is_member = member(bv, func)
        named = [i for i, v in enumerate(pvars) if v.name == "this"][:1]
        if named and (is_member or not mangled(func)):
            storage = _param_storage(func, named[0])
        elif pvars and not is_member:
            # A demangled member signature lists explicit parameters only: its
            # first declared parameter is not this and must not be keyed as it.
            # The this Binary Ninja 6.0 declares on a namespace function is
            # its first real parameter.
            storage = _param_storage(func, 0)
        if storage is None:
            storage = _arg_storage(func, 0)
    keys = []
    for sv in ssa.ssa_vars:
        if ssa.get_ssa_var_definition(sv) is not None:
            continue
        v = sv.var
        if (v.source_type, v.storage) == storage:
            keys.append(_key(sv))
    return keys


def _reads_entry_this(func, ssa):
    """True when the function reads its incoming this: the declared this
    parameter, or the first integer argument register when the demangled
    signature omits this (static members never read it)."""
    params = list(func.parameter_vars)
    if params and params[0].name == "this":
        storage = _param_storage(func, 0)
    else:
        cc = func.calling_convention
        if cc is None or not list(cc.int_arg_regs):
            return False
        storage = _arg_storage(func, 0)
    for sv in ssa.ssa_vars:
        v = sv.var
        if ((v.source_type, v.storage) == storage
                and ssa.get_ssa_var_definition(sv) is None and ssa.get_ssa_var_uses(sv)):
            return True
    return False


def _param_keys(func, ssa, max_index):
    """{index: SSA keys} for parameters 1..max_index-1: the declared parameter
    variable, else the matching integer argument register."""
    params = list(func.parameter_vars)
    cc = func.calling_convention
    regs = list(cc.int_arg_regs) if cc is not None else []
    by_var = {}
    by_reg = {}
    for index in range(1, max_index):
        if index < len(params):
            by_var[params[index]] = index
        elif index < len(regs):
            by_reg[func.arch.get_reg_index(regs[index])] = index
    keys = {}
    if not by_var and not by_reg:
        return keys
    for sv in ssa.ssa_vars:
        if ssa.get_ssa_var_definition(sv) is not None:
            continue
        v = sv.var
        index = by_var.get(v)
        if index is None and v.source_type == _REGISTER:
            index = by_reg.get(v.storage)
        if index is not None:
            keys.setdefault(index, []).append(_key(sv))
    return keys


MAX_PARAM_ROOTS = 6


def _debug_funcs():
    """Function starts to trace, from OORECOVER_DEBUG_FUNCS or tests/debug_funcs.txt."""
    items = os.environ.get("OORECOVER_DEBUG_FUNCS", "").split(",")
    path = os.path.join(os.path.dirname(os.path.dirname(os.path.abspath(__file__))), "tests", "debug_funcs.txt")
    if os.path.isfile(path):
        with open(path) as f:
            items += f.read().split()
    out = set()
    for item in items:
        if item.strip():
            out.add(int(item, 0))
    return out


def _decompose(expr):
    """Address expression -> (kind, key, offset); kind is var/const/stack."""
    offset = 0
    for _ in range(64):
        op = expr.operation
        if op == Op.MLIL_VAR_SSA or op == Op.MLIL_VAR_ALIASED:
            return "var", _key(expr.src), offset
        if op in _CONSTS:
            return "const", None, expr.constant + offset
        if op == Op.MLIL_ADDRESS_OF:
            v = expr.src
            return ("stack", v.storage, offset) if v.source_type == _STACK else None
        if op == Op.MLIL_ADDRESS_OF_FIELD:
            v = expr.src
            return ("stack", v.storage, offset + expr.offset) if v.source_type == _STACK else None
        if op in (Op.MLIL_ADD, Op.MLIL_SUB):
            left, right = expr.left, expr.right
            c = _const(right)
            if c is not None:
                expr = left
            elif op == Op.MLIL_ADD and _const(left) is not None:
                c = _const(left)
                expr = right
            else:
                return None
            offset += c if op == Op.MLIL_ADD else -c
            continue
        return None
    return None


def _walk(root):
    stack = [root]
    while stack:
        e = stack.pop()
        yield e
        for operand in e.operands:
            if isinstance(operand, MediumLevelILInstruction):
                stack.append(operand)
            elif isinstance(operand, list):
                stack.extend(o for o in operand if isinstance(o, MediumLevelILInstruction))


def _const_pointee(t):
    try:
        return t.type_class == TypeClass.PointerTypeClass and bool(t.target.const)
    except Exception:
        return False


_CALLEE_PARAMS = {}


def _callee_param_types(bv, call):
    """Parameter types of a direct call's target by argument position, or
    None. A demangled member signature without this is shifted by one.
    Reading a function's type materialises it, so results are cached for the
    collection pass and only asked for where an address is being passed."""
    target = _call_target(bv, call.dest)
    if target is None:
        return None
    if target in _CALLEE_PARAMS:
        return _CALLEE_PARAMS[target]
    func = bv.get_function_at(target)
    types = None
    if func is not None:
        try:
            params = list(func.type.parameters)
        except Exception:
            params = None
        if params is not None:
            shift = 1 if member(bv, func) and not (params and params[0].name == "this") else 0
            types = [None] * shift + [p.type for p in params]
    _CALLEE_PARAMS[target] = types
    return types


def _escaping_addresses(bv, root, addr_vars):
    """Variables whose address is used other than as a load address or as an
    argument the callee receives as pointer/reference to const: passed to a
    callee that may write through it, stored, or kept beyond a plain copy.
    addr_vars maps SSA keys holding &var to var."""
    def var_of(e):
        op = e.operation
        if op in (Op.MLIL_ADDRESS_OF, Op.MLIL_ADDRESS_OF_FIELD):
            return e.src.identifier
        if op == Op.MLIL_VAR_SSA:
            return addr_vars.get(_key(e.src))
        return None

    if root.operation in _SETS and root.src.operation in (Op.MLIL_ADDRESS_OF, Op.MLIL_ADDRESS_OF_FIELD):
        return   # the copy itself; its uses are judged where they occur
    if root.operation == Op.MLIL_VAR_PHI:
        for sv in root.src:
            var_id = addr_vars.get(_key(sv))
            if var_id is not None:
                yield var_id
        return
    stack = [(root, False)]
    while stack:
        e, under_load = stack.pop()
        op = e.operation
        var_id = var_of(e)
        if var_id is not None:
            if not under_load:
                yield var_id
            continue
        if op in _CALLS:
            ptypes = False
            for i, param in enumerate(e.params):
                if var_of(param) is not None:
                    if ptypes is False:
                        ptypes = _callee_param_types(bv, e)
                    if ptypes is not None and i < len(ptypes) and _const_pointee(ptypes[i]):
                        continue
                stack.append((param, False))
            stack.append((e.dest, False))
            continue
        child_under_load = under_load if op in (Op.MLIL_ADD, Op.MLIL_SUB) else op in _LOADS
        for operand in e.operands:
            if isinstance(operand, MediumLevelILInstruction):
                stack.append((operand, child_under_load))
            elif isinstance(operand, list):
                stack.extend((o, child_under_load) for o in operand
                             if isinstance(o, MediumLevelILInstruction))


def _call_target(bv, expr):
    val = _const(expr)
    if val is None:
        return None
    f = bv.get_function_at(val)
    if f is not None:
        return f.start
    return val if bv.get_symbol_at(val) is not None else None


def _make_name_check(bv, names, short_prefix):
    cache = {}

    def matches(sym):
        raw = sym.raw_name
        return (raw in names or raw.split("@")[0] in names
                or sym.short_name in names or sym.short_name.startswith(short_prefix))

    def check(addr):
        if addr in cache:
            return cache[addr]
        ok = any(matches(s) for s in bv.get_symbols(addr, 1))
        if not ok:
            f = bv.get_function_at(addr)
            ok = f is not None and f.symbol is not None and matches(f.symbol)
        cache[addr] = ok
        return ok

    return check


def collect_function(bv, mem, func, vtable_addrs, is_allocator, is_deallocator, debug=None,
                     slot_functions=frozenset(), sret=False):
    mlil = func.mlil
    if mlil is None:
        return None
    ssa = mlil.ssa_form
    if ssa is None:
        return None
    facts = FunctionFacts(func.start)
    insns = [insn for bb in ssa.basic_blocks for insn in bb]
    if len(insns) <= MAX_THUNK_INSNS:
        # A thunk does nothing but jump: a small deleting destructor that
        # calls the base destructor and tail-calls operator delete is not one.
        calls = [i for i in insns if i.operation in _CALLS]
        if len(calls) == 1 and calls[0].operation == Op.MLIL_TAILCALL_SSA:
            target = _call_target(bv, calls[0].dest)
            if (target is not None and target != func.start
                    and not is_allocator(target) and not is_deallocator(target)):
                facts.tail_target = target
    aliases = {}

    def alias(key, root, off):
        if key in aliases:
            return False
        aliases[key] = (root, off)
        return True

    for key in _this_keys(bv, func, ssa, sret):
        alias(key, ("this",), 0)
    if sret or _returns_indirect(func):
        facts.sret = True       # re-collected past the buffer, or typed so by an earlier pass
    pvars = list(func.parameter_vars)
    if pvars and pvars[0].name == "sret":
        facts.sret = True       # marking of releases before the native return location, kept one release
    facts.entry_this = _reads_entry_this(func, ssa)
    facts.member_of = member_class(bv, func)
    for index, keys in _param_keys(func, ssa, MAX_PARAM_ROOTS).items():
        for key in keys:
            alias(key, ("param", index), 0)

    call_out = {}

    for insn in insns:
        if insn.operation not in _CALLS or not insn.params:
            continue
        target = _call_target(bv, insn.dest)
        size = _const(insn.params[0])
        if size is None or not 0 < size < MAX_ALLOC:
            continue
        if target is not None and is_allocator(target):
            facts.allocs.append(AllocCall(func.start, insn.address, size, target))
            for out in insn.output:
                alias(_key(out), ("alloc", insn.address), 0)
        else:
            for out in insn.output:
                call_out[_key(out)] = (insn.address, size, target or 0)

    sets = []
    phis = []
    spill_writes = {}   # aliased variable -> keys of its SET_VAR_ALIASED writes
    spill_reads = {}    # aliased variable -> keys read (versioned by memory, so undefined in SSA)
    address_taken = set()
    addr_vars = {}      # SSA key holding &var -> var
    for insn in insns:
        if insn.operation in _SETS and insn.src.operation in (Op.MLIL_ADDRESS_OF, Op.MLIL_ADDRESS_OF_FIELD):
            addr_vars[_key(insn.dest)] = insn.src.src.identifier
    for insn in insns:
        op = insn.operation
        if op in _SETS:
            d = _decompose(insn.src)
            if d is not None:
                sets.append((_key(insn.dest), d))
            if op == Op.MLIL_SET_VAR_ALIASED:
                spill_writes.setdefault(insn.dest.var.identifier, []).append(_key(insn.dest))
        elif op == Op.MLIL_VAR_PHI:
            phis.append((_key(insn.dest), [_key(s) for s in insn.src]))
        for sub in _walk(insn):
            if sub.operation == Op.MLIL_VAR_ALIASED:
                spill_reads.setdefault(sub.src.var.identifier, set()).add(_key(sub.src))
        address_taken.update(_escaping_addresses(bv, insn, addr_vars))
        if op == Op.MLIL_SET_VAR_ALIASED_FIELD or op == Op.MLIL_VAR_ALIASED_FIELD:
            address_taken.add(insn.dest.var.identifier if op == Op.MLIL_SET_VAR_ALIASED_FIELD
                              else insn.src.var.identifier)

    def propagate():
        for _ in range(MAX_PASSES):
            changed = False
            for dest, (kind, key, off) in sets:
                if kind == "var":
                    base = aliases.get(key)
                    if base is not None:
                        changed |= alias(dest, base[0], base[1] + off)
                elif kind == "stack":
                    changed |= alias(dest, ("stack", key), off)
                elif mem.is_data(off):
                    changed |= alias(dest, ("global", off), 0)
            for dest, srcs in phis:
                bases = [aliases.get(s) for s in srcs]
                if bases and all(b is not None and b == bases[0] for b in bases):
                    changed |= alias(dest, bases[0][0], bases[0][1])
            # A spill slot whose address never escapes is written only by its
            # SET_VAR_ALIASED instructions; when those agree, every read of it
            # (versioned by memory, hence undefined in SSA) holds the same object.
            for var_id, reads in spill_reads.items():
                if var_id in address_taken:
                    continue
                writes = spill_writes.get(var_id)
                if not writes:
                    continue
                bases = [aliases.get(w) for w in writes]
                if not all(b is not None and b == bases[0] for b in bases):
                    continue
                for key in reads:
                    changed |= alias(key, bases[0][0], bases[0][1])
            if not changed:
                return

    propagate()

    def resolve(expr):
        d = _decompose(expr)
        if d is None:
            return None
        kind, key, off = d
        if kind == "var":
            base = aliases.get(key)
            return None if base is None else (base[0], base[1] + off)
        if kind == "stack":
            return ("stack", key), off
        return ("global", off), 0

    seeded = False
    for insn in insns:
        if insn.operation not in _STORES:
            continue
        val = _const(insn.src)
        if val is None or val not in vtable_addrs:
            continue
        d = _decompose(insn.dest)
        if d is None or d[0] != "var" or d[1] in aliases:
            continue
        if d[1] in call_out:
            insn_addr, size, callee = call_out[d[1]]
            facts.allocs.append(AllocCall(func.start, insn_addr, size, callee))
            seeded |= alias(d[1], ("alloc", insn_addr), 0)
        else:
            seeded |= alias(d[1], ("var", d[1]), 0)
    if seeded:
        propagate()

    def resolve_field(expr, field_offset):
        r = resolve(expr)
        return None if r is None else (r[0], r[1] + field_offset)

    ptrsize = mem.ptrsize
    vptr_vars = {}    # ssa key -> (root, object offset) whose vtable pointer it holds
    fnptr_vars = {}   # ssa key -> (root, object offset, slot)

    def split_add(expr):
        if expr.operation in (Op.MLIL_ADD, Op.MLIL_SUB):
            c = _const(expr.right)
            if c is not None:
                return expr.left, (c if expr.operation == Op.MLIL_ADD else -c)
            if expr.operation == Op.MLIL_ADD:
                c = _const(expr.left)
                if c is not None:
                    return expr.right, c
        return expr, 0

    def vptr_of(expr):
        """(root, object offset) when expr yields the vtable pointer of an object."""
        op = expr.operation
        if op == Op.MLIL_VAR_SSA:
            return vptr_vars.get(_key(expr.src))
        if op in _LOADS:
            return resolve_field(expr.src, expr.offset if op == Op.MLIL_LOAD_STRUCT_SSA else 0)
        return None

    def slot_of(expr):
        """(root, object offset, slot) when expr yields a function pointer
        loaded from an object's vtable."""
        op = expr.operation
        if op == Op.MLIL_VAR_SSA:
            return fnptr_vars.get(_key(expr.src))
        if op not in _LOADS:
            return None
        base, k = split_add(expr.src)
        k += expr.offset if op == Op.MLIL_LOAD_STRUCT_SSA else 0
        vp = vptr_of(base)
        if vp is None or k < 0 or k % ptrsize:
            return None
        return vp[0], vp[1], k // ptrsize

    for _ in range(MAX_PASSES):
        changed = False
        for insn in insns:
            op = insn.operation
            if op == Op.MLIL_VAR_PHI:
                # A speculatively devirtualised call reloads the vtable on
                # its indirect branch and merges it with the first load.
                key = _key(insn.dest)
                srcs = [_key(s) for s in insn.src]
                for table in (vptr_vars, fnptr_vars):
                    vals = [table.get(s) for s in srcs]
                    if key not in table and vals and vals[0] is not None and all(v == vals[0] for v in vals):
                        table[key] = vals[0]
                        changed = True
                continue
            if op not in _SETS:
                continue
            key = _key(insn.dest)
            if key in vptr_vars or key in fnptr_vars:
                continue
            vp = vptr_of(insn.src)
            if vp is not None:
                vptr_vars[key] = vp
                changed = True
                continue
            fp = slot_of(insn.src)
            if fp is not None:
                fnptr_vars[key] = fp
                changed = True
        if not changed:
            break

    if debug is not None:
        print = debug
        print("[oorecover] debug %#x this keys %s params %s" % (
            func.start, _this_keys(bv, func, ssa), _param_keys(func, ssa, MAX_PARAM_ROOTS)))
        print("[oorecover] debug %#x spill writes %s reads %s address_taken %s" % (
            func.start, spill_writes, {k: sorted(v) for k, v in spill_reads.items()}, address_taken))
        for insn in insns:
            if insn.operation in (Op.MLIL_SET_VAR_ALIASED, Op.MLIL_SET_VAR_ALIASED_FIELD) or any(
                    sub.operation in (Op.MLIL_VAR_ALIASED, Op.MLIL_VAR_ALIASED_FIELD,
                                      Op.MLIL_ADDRESS_OF, Op.MLIL_ADDRESS_OF_FIELD) for sub in _walk(insn)):
                print("[oorecover] debug %#x aliased insn %#x %s: %s" % (
                    func.start, insn.address, insn.operation.name, insn))
        print("[oorecover] debug %#x aliases %s" % (func.start, sorted(aliases.items())[:20]))
        print("[oorecover] debug %#x vptr_vars %s" % (func.start, vptr_vars))
        print("[oorecover] debug %#x fnptr_vars %s" % (func.start, fnptr_vars))
        for insn in insns:
            if insn.operation in _VCALL_SITES:
                print("[oorecover] debug %#x call %#x dest %s (%s) -> %s" % (
                    func.start, insn.address, insn.dest, insn.dest.operation.name, slot_of(insn.dest)))
    for insn in insns:
        # A jump through a vtable slot is a tail dispatch Binary Ninja has not
        # (yet) classified as a tail call.
        if insn.operation in _VCALL_SITES:
            fp = slot_of(insn.dest)
            if fp is not None:
                facts.vcalls.append(VirtualCall(func.start, insn.address, fp[0], fp[1], fp[2]))

    facts.reach = max([off for root, off in aliases.values() if root == ("this",)] + [0])

    for insn in insns:
        op = insn.operation
        for sub in _walk(insn):
            sop = sub.operation
            if sop in _LOADS:
                r = resolve_field(sub.src, sub.offset if sop == Op.MLIL_LOAD_STRUCT_SSA else 0)
                if r is not None:
                    facts.accesses.append(MemberAccess(
                        func.start, sub.address, r[0], r[1], sub.size, False))
            elif sop in (Op.MLIL_VAR_SSA, Op.MLIL_VAR_ALIASED) or sop in _FIELD_VARS:
                v = sub.src.var
                if v.source_type == _STACK:
                    field = sub.offset if sop in _FIELD_VARS else 0
                    facts.stack_accesses.append((sub.address, v.storage + field, sub.size, False))
        if op in _STORES:
            r = resolve_field(insn.dest, insn.offset if op == Op.MLIL_STORE_STRUCT_SSA else 0)
            if r is None:
                continue
            val = _const(insn.src)
            if val is not None and val in vtable_addrs:
                facts.installs.append(VtableInstall(
                    func.start, insn.address, insn.instr_index, val, r[0], r[1]))
            else:
                hint = "ptr" if val is not None and val != 0 and mem.is_mapped(val) else "int"
                facts.accesses.append(MemberAccess(
                    func.start, insn.address, r[0], r[1], insn.size, True, hint))
        elif op in _SETS or op in _FIELD_SETS:
            # Stack objects: plain stores, or field stores once Binary Ninja
            # has given the variable a structure type.
            dv = insn.dest.var
            if dv.source_type != _STACK:
                continue
            field = insn.offset if op in _FIELD_SETS else 0
            val = _const(insn.src)
            if val is not None and val in vtable_addrs:
                facts.installs.append(VtableInstall(
                    func.start, insn.address, insn.instr_index, val,
                    ("stack", dv.storage + field), 0))
            else:
                facts.stack_accesses.append((insn.address, dv.storage + field, insn.size, True))
        elif op in _CALLS:
            target = _call_target(bv, insn.dest)
            if target is None or not insn.params or is_allocator(target):
                continue
            r = resolve(insn.params[0])
            if r is not None:
                facts.calls.append(ThisCall(func.start, insn.address, target, r[0], r[1],
                                            is_deallocator(target)))
            if is_deallocator(target):
                continue
            for index, param in enumerate(insn.params[:MAX_PARAM_ROOTS]):
                r = resolve(param)
                if r is not None and r[1] >= 0:
                    facts.argpasses.append(ArgPass(func.start, insn.address, target, index, r[0], r[1]))
    if not sret and func.start in slot_functions and not facts.installs and any(
            a.root == ("this",) and a.offset == 0 and a.is_write for a in facts.accesses):
        # A virtual method never writes its own vtable slot: the register it
        # was keyed on holds a struct returned by value (sret); this is the
        # next argument register.
        again = collect_function(bv, mem, func, vtable_addrs, is_allocator, is_deallocator,
                                 debug, slot_functions, sret=True)
        if again is not None:
            again.sret = True
            again.sret_size = max(a.offset + a.size for a in facts.accesses
                                  if a.root == ("this",) and a.is_write)
            return again
    return facts


def _param_class_names(func):
    """Names of the structs the function's pointer parameters point to."""
    out = []
    try:
        for p in func.type.parameters:
            t = p.type
            if t.type_class != TypeClass.PointerTypeClass:
                continue
            target = t.target
            if target.type_class == TypeClass.NamedTypeReferenceClass:
                out.append(str(target.name))
    except Exception:
        pass
    return out


def _typed_param_functions(bv, class_names, log=print):
    """Functions whose signature takes a pointer to a known class: virtual
    calls through such parameters resolve to the class and its subclasses."""
    if not class_names:
        return set()
    t0 = time.time()
    starts = set()
    for func in bv.functions:
        if any(n in class_names for n in _param_class_names(func)):
            starts.add(func.start)
    log("[oorecover] %d functions take a known class pointer (%.1fs)" % (len(starts), time.time() - t0))
    return starts


def _member_functions(bv):
    """Functions whose mangled name makes them a class member. Non-virtual
    methods are reached through no vtable yet call virtual methods on this;
    members of classes without any vtable are the only evidence those
    classes exist."""
    return {func.start for func in bv.functions if member(bv, func)}


def _relevant_functions(bv, tables, is_allocator):
    """Functions that can contribute facts: vtable slot functions, functions
    referencing a vtable (constructors, destructors, inlined construction
    sites) and callers of allocators. Everything else is skipped."""
    starts = set()
    for t in tables:
        starts.update(t.functions)
        for ref in bv.get_code_refs(t.address):
            if ref.function is not None:
                starts.add(ref.function.start)
    for sym in bv.get_symbols():
        if sym.type in (SymbolType.FunctionSymbol, SymbolType.ImportedFunctionSymbol,
                        SymbolType.ImportAddressSymbol, SymbolType.ExternalSymbol) \
                and is_allocator(sym.address):
            for ref in bv.get_code_refs(sym.address):
                if ref.function is not None:
                    starts.add(ref.function.start)
    return starts


def collect_all(bv, mem, abi, tables, log=print, progress=None, cancelled=None, extra=(),
                class_names=()):
    _CALLEE_PARAMS.clear()
    is_allocator = _make_name_check(bv, abi.allocators, "operator new")
    is_deallocator = _make_name_check(bv, abi.deallocators, "operator delete")
    vtable_addrs = {t.address for t in tables}
    slot_functions = frozenset(fn for t in tables for fn in t.functions)
    class_names = {t.rtti_name for t in tables if t.rtti_name} | set(class_names or ())
    scan_scopes(bv, class_names, log)
    debug_funcs = _debug_funcs()
    pending = sorted(_relevant_functions(bv, tables, is_allocator) | set(extra)
                     | _typed_param_functions(bv, class_names, log)
                     | _member_functions(bv))
    result = {}
    seen = set()
    no_il = 0
    failed = 0
    total = 0
    while pending:
        addr = pending.pop()
        if addr in seen:
            continue
        seen.add(addr)
        if cancelled and cancelled():
            break
        total += 1
        if progress and total % 100 == 0:
            progress("collecting facts %d (%d queued)" % (total, len(pending)))
        func = bv.get_function_at(addr)
        if func is None:
            continue
        try:
            f = collect_function(bv, mem, func, vtable_addrs, is_allocator, is_deallocator,
                                 log if func.start in debug_funcs else None, slot_functions)
        except Exception:
            failed += 1
            if failed <= 5:
                log("[oorecover] collect failed in %#x:\n%s" % (addr, traceback.format_exc()))
            continue
        if f is None:
            no_il += 1
            continue
        if f.tail_target is not None and f.tail_target not in seen:
            pending.append(f.tail_target)
        if not f.empty():
            result[addr] = f
    log("[oorecover] facts from %d of %d relevant functions (%d without IL, %d failed)"
        % (len(result), total, no_il, failed))
    return result
