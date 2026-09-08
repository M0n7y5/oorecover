"""Facts produced by the scanners and the collector, consumed by the model.

Object roots used by collector facts:
  ("this",)           the function's first parameter
  ("alloc", insn)     result of an allocation call at insn
  ("global", addr)    an absolute address
  ("stack", storage)  frame offset of a local object
  ("var", key)        unknown SSA variable seeded by a vtable store
  ("member", root, off) the pointer loaded from that member of root (virtual calls only)
"""
from dataclasses import dataclass, field
from typing import Optional


@dataclass
class BaseRef:
    name: Optional[str]
    offset: Optional[int]      # None for virtual bases (offset known only at runtime)
    virtual: bool = False
    typeinfo: Optional[int] = None


@dataclass
class VtableInfo:
    address: int               # address point (slot 0)
    slots: list                # code address per slot; None for pure/imported slots
    typeinfo_addr: Optional[int] = None
    object_offset: int = 0     # sub-object this table serves (0 = primary)
    rtti_name: Optional[str] = None
    bases: list = field(default_factory=list)      # [BaseRef], from RTTI
    unresolved: list = field(default_factory=list) # code slots with no function yet
    referenced: bool = False   # RTTI-backed or directly referenced from code
    sym_addr: Optional[int] = None  # the vtable symbol this table belongs to
    sym_name: Optional[str] = None  # class name decoded from that symbol
    construction: Optional[str] = None  # derived class whose constructors use this construction vtable
    vbases: list = field(default_factory=list)  # [BaseRef] every virtual base of the class, direct or
                                                # indirect, in vbase-offset order; offset when the header gave it

    @property
    def functions(self):
        return [s for s in self.slots if s is not None]

    @property
    def has_rtti(self):
        return self.typeinfo_addr is not None


@dataclass
class VtableInstall:
    func: int
    insn: int
    order: int                 # MLIL instruction index, orders stores in a function
    vtable: int
    root: tuple
    offset: int


@dataclass
class MemberAccess:
    func: int
    insn: int
    root: tuple
    offset: int
    size: int
    is_write: bool
    hint: str = "int"          # "int" | "ptr"
    src_root: tuple = None     # object root whose offset 0 a write stores; ("const", v) for a bare constant


@dataclass
class ThisCall:
    """A direct call whose first argument is root+offset."""
    caller: int
    insn: int
    callee: int
    root: tuple
    offset: int
    dealloc: bool = False    # callee is operator delete / free


@dataclass
class ArgPass:
    """A direct call whose argument `index` is root+offset."""
    caller: int
    insn: int
    callee: int
    index: int
    root: tuple
    offset: int


@dataclass
class VirtualCall:
    """An indirect call through the vtable of the object at root+object_offset."""
    func: int
    insn: int
    root: tuple
    object_offset: int
    slot: int                # slot index within that sub-object's vtable
    arg0: tuple = None       # (root, offset) of the first argument when it is not the object called on


@dataclass
class AllocCall:
    func: int
    insn: int
    size: int
    callee: int
