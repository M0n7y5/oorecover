"""Memory access helpers shared by the ABI parsers, plus ABI detection."""
import bisect
import struct

from binaryninja.enums import Endianness, SectionSemantics, SymbolType

_DEFAULT_SEMANTICS = int(SectionSemantics.DefaultSectionSemantics)
_CODE_SEMANTICS = int(SectionSemantics.ReadOnlyCodeSectionSemantics)
_DATA_SEMANTICS = (int(SectionSemantics.ReadOnlyDataSectionSemantics),
                   int(SectionSemantics.ReadWriteDataSectionSemantics))

# Sections that hold function pointers but never vtables.
SKIP_SECTION_PREFIXES = (
    ".got", ".plt", ".init_array", ".fini_array", ".ctors", ".dtors",
    ".dynamic", ".dynsym", ".dynstr", ".eh_frame", ".gcc_except_table",
    ".idata", ".edata", ".pdata", ".xdata", ".reloc", ".rsrc", ".tls",
    ".debug", ".comment", ".note", ".hash", ".gnu", ".rela", ".rel.",
    ".interp", ".symtab", ".strtab", ".shstrtab", ".init", ".fini",
    ".bss", "__la_symbol_ptr", "__nl_symbol_ptr", "__got", "__mod_init",
)

PURE_SLOT_NAMES = {"__cxa_pure_virtual", "__cxa_deleted_virtual", "_purecall"}

_IMPORT_SYMBOLS = (SymbolType.ImportAddressSymbol, SymbolType.ImportedFunctionSymbol,
                   SymbolType.ImportedDataSymbol, SymbolType.ExternalSymbol)


class Memory:
    """Cached section/segment map with endianness-aware reads.

    Sections decide what is code and what is data; segment flags are only a
    fallback for addresses no section covers. Binaries linked with two
    PT_LOAD segments keep .rodata inside the executable segment, so segment
    flags alone would reject every typeinfo name pointer."""

    def __init__(self, bv):
        self.bv = bv
        self.ptrsize = bv.address_size
        self.big_endian = bv.endianness == Endianness.BigEndian
        self._prefix = ">" if self.big_endian else "<"
        segs = sorted((s.start, s.end, bool(s.executable), bool(s.readable))
                      for s in bv.segments)
        self._segs = segs
        self._starts = [s[0] for s in segs]
        secs = []
        for s in bv.sections.values():
            if s.end > s.start:
                secs.append((s.start, s.end, int(s.semantics)))
        secs.sort()
        self._secs = secs
        self._sec_starts = [s[0] for s in secs]

    def segment(self, addr):
        if addr is None:
            return None
        i = bisect.bisect_right(self._starts, addr) - 1
        if i < 0:
            return None
        seg = self._segs[i]
        return seg if seg[0] <= addr < seg[1] else None

    def section_semantics(self, addr):
        """Semantics of the section covering addr; None when no section does
        or the section carries no semantics."""
        if addr is None or not self._secs:
            return None
        i = bisect.bisect_right(self._sec_starts, addr) - 1
        if i < 0:
            return None
        start, end, sem = self._secs[i]
        if start <= addr < end and sem != _DEFAULT_SEMANTICS:
            return sem
        return None

    def is_code(self, addr):
        sem = self.section_semantics(addr)
        if sem is not None:
            return sem == _CODE_SEMANTICS
        seg = self.segment(addr)
        return seg is not None and seg[2]

    def is_data(self, addr):
        sem = self.section_semantics(addr)
        if sem is not None:
            return sem in _DATA_SEMANTICS
        seg = self.segment(addr)
        return seg is not None and seg[3] and not seg[2]

    def is_mapped(self, addr):
        return self.segment(addr) is not None

    def read(self, addr, n):
        if addr is None or addr < 0:
            return None
        data = self.bv.read(addr, n)
        if data is None or len(data) != n:
            return None
        return data

    def read_uint(self, addr, n):
        data = self.read(addr, n)
        if data is None:
            return None
        return int.from_bytes(data, "big" if self.big_endian else "little")

    def read_int(self, addr, n):
        val = self.read_uint(addr, n)
        if val is None:
            return None
        return sign(val, n * 8)

    def read_ptr(self, addr):
        """Pointer-sized read. A zero slot covered by a relocation is resolved
        through the relocation: executables linked with exported (weak)
        typeinfos keep the value in the RELA addend/symbol, and Binary Ninja
        does not apply those."""
        val = self.read_uint(addr, self.ptrsize)
        if val:
            return val
        if val is None:
            return None
        return self._relocated(addr)

    def _relocated(self, addr):
        try:
            relocs = self.bv.relocations_at(addr)
        except Exception:
            return 0
        for r in relocs:
            try:
                target = r.target
                if target and self.is_mapped(target):
                    return target
                sym = r.symbol
                if sym is None:
                    continue
                addend = r.info.addend or 0
                for s in self.bv.get_symbols_by_raw_name(sym.raw_name):
                    if s.type == SymbolType.DataSymbol and self.is_data(s.address):
                        return s.address + addend
                if sym.address:
                    return sym.address + addend
            except Exception:
                continue
        return 0

    def read_cstring(self, addr, limit=512):
        chunk = self.bv.read(addr, limit)
        if not chunk:
            return None
        end = chunk.find(b"\x00")
        if end < 0:
            return None
        return bytes(chunk[:end])

    def unpack_ptrs(self, data):
        fmt = self._prefix + ("Q" if self.ptrsize == 8 else "I")
        usable = len(data) - len(data) % self.ptrsize
        return [v[0] for v in struct.iter_unpack(fmt, data[:usable])]

    def is_function_start(self, addr):
        return self.bv.get_function_at(addr) is not None

    def symbol_name(self, addr):
        sym = self.bv.get_symbol_at(addr)
        return None if sym is None else sym.raw_name

    def is_pure_slot(self, slot_addr, entry):
        """A slot that names an imported helper (pure virtual, deleted, or an
        unresolved relocation) rather than a function in this image."""
        if entry == 0:
            return bool(self.bv.relocations_at(slot_addr))
        for sym in self.bv.get_symbols(entry, 1):
            if sym.type in _IMPORT_SYMBOLS or sym.raw_name in PURE_SLOT_NAMES:
                return True
        return False


def sign(val, bits):
    if val >= 1 << (bits - 1):
        val -= 1 << bits
    return val


def _referenced(bv, addr):
    for _ref in bv.get_code_refs(addr, max_items=1):
        return True
    for _ref in bv.get_data_refs(addr, max_items=1):
        return True
    return False


def read_slots(mem, ap, max_slots, allow_null=False, split_on_refs=False):
    """Read vtable slots starting at address point ap.

    Returns (slots, unresolved): slots holds code addresses, or None for
    pure/imported entries; unresolved lists code addresses that are not yet
    function starts. With allow_null (tables proven by RTTI) plain zero
    entries are slots too: compilers null the destructor slots of abstract
    classes. A zero followed by a data pointer is the next table's header,
    not a slot. Trailing zero padding is trimmed. With split_on_refs (tables
    with no header at all, MSVC without RTTI) a later slot that code or data
    refers to is the next table's address point.
    """
    kinds = []
    slots = []
    unresolved = []
    for i in range(max_slots):
        addr = ap + i * mem.ptrsize
        entry = mem.read_ptr(addr)
        if entry is None:
            break
        if split_on_refs and i > 0 and _referenced(mem.bv, addr):
            break
        if entry != 0 and mem.is_code(entry):
            kinds.append("func")
            slots.append(entry)
            if not mem.is_function_start(entry):
                unresolved.append(entry)
            continue
        if mem.is_pure_slot(addr, entry):
            kinds.append("pure")
            slots.append(None)
            continue
        if allow_null and entry == 0:
            after = mem.read_ptr(addr + mem.ptrsize)
            if after is not None and after != 0 and not mem.is_code(after) and mem.is_data(after):
                break
            kinds.append("null")
            slots.append(None)
            continue
        break
    while kinds and kinds[-1] == "null":
        kinds.pop()
        slots.pop()
    return slots, unresolved


def iter_data_sections(bv, mem):
    for section in bv.sections.values():
        name = section.name
        if name.startswith(SKIP_SECTION_PREFIXES):
            continue
        if section.end <= section.start:
            continue
        if not mem.is_data(section.start):
            continue
        yield section


def detect_abi(bv):
    for sym in bv.get_symbols():
        raw = sym.raw_name
        if raw.startswith(("_ZTV", "_ZTI", "_ZTS")):
            return "itanium"
        if raw.startswith(("??_7", "??_R")):
            return "msvc"
    return "msvc" if bv.view_type == "PE" else "itanium"
