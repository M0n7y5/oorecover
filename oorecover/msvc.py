"""MSVC C++ ABI: vftable layout and RTTI parsing.

Vftable layout around the address point AP: AP - ptr holds a pointer to the
RTTICompleteObjectLocator (COL). x64 COLs (signature 1) hold image-relative
offsets and a self RVA; x86 COLs (signature 0) hold absolute pointers.
  COL: u32 signature, u32 offset (sub-object offset), u32 cdOffset,
       ref TypeDescriptor, ref ClassHierarchyDescriptor, [u32 selfRVA]
  TypeDescriptor: ptr type_info vftable, ptr spare, char name[] (".?AV...")
  ClassHierarchyDescriptor: u32 signature, u32 attributes, u32 numBases,
       ref BaseClassArray (array of ref BaseClassDescriptor, self first)
  BaseClassDescriptor: ref TypeDescriptor, u32 numContainedBases,
       i32 mdisp, i32 pdisp, i32 vdisp, u32 attributes, ref CHD
"""
import re

from binaryninja.enums import SymbolType

from .abi import read_slots
from .facts import BaseRef, VtableInfo
from .names import demangle

MAX_SLOTS = 4096
MAX_BASES = 256
MAX_OBJECT = 1 << 24

ALLOCATORS = {
    "??2@YAPEAX_K@Z", "??2@YAPAXI@Z", "??_U@YAPEAX_K@Z", "??_U@YAPAXI@Z",
    "??2@YAPEAX_KAEBUnothrow_t@std@@@Z", "??2@YAPAXIABUnothrow_t@std@@@Z",
    "malloc", "_malloc_base", "calloc",
}

DEALLOCATORS = {
    "??3@YAXPEAX@Z", "??3@YAXPEAX_K@Z", "??_V@YAXPEAX@Z", "??_V@YAXPEAX_K@Z",
    "??3@YAXPAX@Z", "??3@YAXPAXI@Z", "??_V@YAXPAX@Z", "??_V@YAXPAXI@Z",
    "free", "_free_base",
}

_TD_NAME_RE = re.compile(r"^\.\?A[VUTW][0-9A-Za-z_@?$]+@@$")


_BASIC_TYPES = {"D": "char", "E": "unsigned char", "F": "short", "G": "unsigned short",
                "H": "int", "I": "unsigned int", "J": "long", "K": "unsigned long",
                "M": "float", "N": "double", "X": "void", "_N": "bool", "_J": "__int64",
                "_K": "unsigned __int64", "_W": "wchar_t"}


def _parse_qualified(s, pos):
    """Parse an MSVC qualified name (components terminated by '@', list by '@')
    starting at pos. Returns (name, new_pos) or (None, pos)."""
    parts = []
    while pos < len(s):
        if s.startswith("@", pos):
            return ("::".join(reversed(parts)) if parts else None), pos + 1
        if s.startswith("?$", pos):
            end = s.find("@", pos + 2)
            if end < 0:
                return None, pos
            base = s[pos + 2:end]
            args, pos = _parse_template_args(s, end + 1)
            if args is None:
                return None, pos
            parts.append("%s<%s>" % (base, ", ".join(args)))
        elif s.startswith("?A0x", pos):
            end = s.find("@", pos)
            if end < 0:
                return None, pos
            parts.append("(anonymous namespace)")
            pos = end + 1
        else:
            end = s.find("@", pos)
            if end < 0 or end == pos:
                return None, pos
            parts.append(s[pos:end])
            pos = end + 1
    return None, pos


def _parse_number(s, pos):
    """MSVC encoded number after '$0': a digit means value+1, letters A-P
    are hex nibbles terminated by '@'."""
    if pos < len(s) and s[pos].isdigit():
        return str(int(s[pos]) + 1), pos + 1
    end = s.find("@", pos)
    if end < 0:
        return None, pos
    digits = s[pos:end]
    if digits and all("A" <= ch <= "P" for ch in digits):
        return str(int("".join("%x" % (ord(ch) - ord("A")) for ch in digits), 16)), end + 1
    return None, pos


def _parse_type(s, pos):
    """Parse one type in a template argument list."""
    for prefix, suffix in (("PEA", "*"), ("PEB", " const*"), ("AEA", "&"), ("AEB", " const&"),
                           ("PA", "*"), ("PB", " const*"), ("AA", "&"), ("AB", " const&")):
        if s.startswith(prefix, pos):
            inner, pos = _parse_type(s, pos + len(prefix))
            return (None, pos) if inner is None else (inner + suffix, pos)
    if s[pos] in "VUT":
        return _parse_qualified(s, pos + 1)
    if s.startswith("W4", pos):
        return _parse_qualified(s, pos + 2)
    if s.startswith("_", pos) and s[pos:pos + 2] in _BASIC_TYPES:
        return _BASIC_TYPES[s[pos:pos + 2]], pos + 2
    if s[pos] in _BASIC_TYPES:
        return _BASIC_TYPES[s[pos]], pos + 1
    return None, pos


def _parse_template_args(s, pos):
    args = []
    while pos < len(s):
        if s.startswith("@", pos):
            return args, pos + 1
        if s.startswith("$$V", pos):
            pos += 3
        elif s.startswith("$0", pos):
            value, pos = _parse_number(s, pos + 2)
            if value is None:
                return None, pos
            args.append(value)
        else:
            name, pos = _parse_type(s, pos)
            if name is None:
                return None, pos
            args.append(name)
    return None, pos


def demangle_typename(raw):
    """Fallback demangler for TypeDescriptor names: '.?AVDog@zoo@@' -> 'zoo::Dog',
    including class-typed and basic-typed template arguments."""
    if not raw or not raw.startswith(".?A") or len(raw) < 5:
        return None
    body = raw[3:]
    if body.startswith("W4"):
        body = body[2:]
    elif body[0] in "VUT":
        body = body[1:]
    else:
        return None
    name, pos = _parse_qualified(body, 0)
    if name is None or pos != len(body):
        return None
    return name


def _bn_demangle_ms(bv, mangled, drop_last):
    try:
        result = demangle(bv, mangled, "msvc")
    except Exception:
        return None
    if result is None:
        return None
    names = [str(n) for n in result[1]]
    if not names or names[0].startswith("?"):
        return None
    if drop_last and len(names) > 1:
        names = names[:-1]
    name = "::".join(names)
    return name or None


def demangle_name(bv, raw):
    """Demangle a TypeDescriptor name. Tries the RTTI descriptor form, then
    the vftable form (which Binary Ninja handles for more template shapes),
    then the local fallback."""
    if bv is not None and raw.startswith(".?A") and len(raw) > 4:
        name = _bn_demangle_ms(bv, "??_R0" + raw + "@8", True)
        if name and "RTTI" not in name:
            return name
        inner = raw[4:] if raw[3] != "W" else raw[5:]
        name = _bn_demangle_ms(bv, "??_7" + inner + "6B@", True)
        if name and "vftable" not in name:
            return name
    return demangle_typename(raw)


def _fail(why, reason):
    if why is not None:
        why.append(reason)
    return None


class MSVC:
    name = "msvc"
    allocators = ALLOCATORS
    deallocators = DEALLOCATORS

    def __init__(self, bv, mem, log=print):
        self.bv = bv
        self.mem = mem
        self.log = log
        self.image_base = bv.start
        self._td_cache = {}
        self._chd_cache = {}
        self._col_cache = {}
        self._td_chd = {}     # type descriptor -> its class hierarchy descriptor, from a base entry

    def _ref(self, addr):
        """Read a pointer-or-RVA field."""
        if self.mem.ptrsize == 8:
            rva = self.mem.read_uint(addr, 4)
            return None if rva is None else self.image_base + rva
        return self.mem.read_ptr(addr)

    def parse_td(self, td):
        if td in self._td_cache:
            return self._td_cache[td]
        self._td_cache[td] = None
        p = self.mem.ptrsize
        if not self.mem.is_data(td):
            return None
        raw = self.mem.read_cstring(td + 2 * p)
        if raw is None:
            return None
        try:
            raw = raw.decode("ascii")
        except UnicodeDecodeError:
            return None
        if not _TD_NAME_RE.match(raw):
            return None
        name = demangle_name(self.bv, raw) or raw
        self._td_cache[td] = name
        return name

    def parse_col(self, col):
        """Returns (object_offset, td_addr, chd_addr) or None."""
        if not self.mem.is_data(col):
            return None
        sig = self.mem.read_uint(col, 4)
        offset = self.mem.read_uint(col + 4, 4)
        if sig is None or offset is None or offset >= MAX_OBJECT:
            return None
        if self.mem.ptrsize == 8:
            if sig != 1:
                return None
            self_rva = self.mem.read_uint(col + 20, 4)
            if self_rva is None or self.image_base + self_rva != col:
                return None
        elif sig != 0:
            return None
        td = self._ref(col + 12)
        chd = self._ref(col + 16)
        if td is None or chd is None or not self.mem.is_data(td) or not self.mem.is_data(chd):
            return None
        return offset, td, chd

    def parse_chd(self, chd):
        """Returns (direct bases, virtual bases) as [BaseRef] lists. The base
        class array lists every base in depth-first order, each followed by
        the bases it contains; an entry reached through a virtual base
        carries a vbtable displacement instead of a fixed offset. Virtual
        base offsets live in the vbtable, not in the RTTI, so they stay None."""
        if chd in self._chd_cache:
            return self._chd_cache[chd]
        self._chd_cache[chd] = ([], [])
        sig = self.mem.read_uint(chd, 4)
        count = self.mem.read_uint(chd + 8, 4)
        bca = self._ref(chd + 12)
        if sig != 0 or count is None or not 1 <= count <= MAX_BASES or not self.mem.is_data(bca):
            return [], []
        refsize = 4 if self.mem.ptrsize == 8 else self.mem.ptrsize
        bases, vbases, seen = [], [], set()
        next_direct = 1
        for i in range(1, count):
            bcd = self._ref(bca + i * refsize)
            if bcd is None or not self.mem.is_data(bcd):
                break
            td = self._ref(bcd)
            contained = self.mem.read_uint(bcd + 4, 4)
            mdisp = self.mem.read_int(bcd + 8, 4)
            pdisp = self.mem.read_int(bcd + 12, 4)
            if td is None or contained is None or mdisp is None or pdisp is None:
                break
            name = self.parse_td(td)
            virtual = pdisp != -1
            attributes = self.mem.read_uint(bcd + 20, 4) or 0
            if attributes & 0x40 and td not in self._td_chd:    # BCD_HASPCHD
                pchd = self._ref(bcd + 24)
                if pchd is not None and self.mem.is_data(pchd):
                    self._td_chd[td] = pchd
            if i == next_direct:
                bases.append(BaseRef(name, None if virtual else mdisp, virtual, td))
                next_direct = i + 1 + contained
            if virtual and td not in seen:
                seen.add(td)
                vbases.append(BaseRef(name, None, True, td))
        self._chd_cache[chd] = (bases, vbases)
        return bases, vbases

    def rtti_bases(self, td):
        """Direct bases of the class td describes, from the hierarchy
        descriptor a base entry of some derived class pointed at, whether
        or not the class has a vftable of its own; None when unknown."""
        chd = self._td_chd.get(td)
        return self.parse_chd(chd)[0] if chd is not None else None

    def parse_vtable_at(self, ap, why=None, trusted=False, bound=None):
        p = self.mem.ptrsize
        col = self.mem.read_ptr(ap - p)
        if col is None:
            return _fail(why, "header unreadable")
        name, bases, vbases, td, offset = None, [], [], None, 0
        parsed = self.parse_col(col) if col else None
        if parsed is not None:
            offset, td, chd = parsed
            name = self.parse_td(td)
            if name is None:
                return _fail(why, "type descriptor %#x unparsable" % td)
            bases, vbases = self.parse_chd(chd)
        limit = MAX_SLOTS if bound is None else max(0, min(MAX_SLOTS, (bound - ap) // p))
        slots, unresolved = read_slots(self.mem, ap, limit,
                                       allow_null=parsed is not None or trusted,
                                       split_on_refs=parsed is None)
        if not slots or (parsed is None and not trusted
                         and not any(s is not None for s in slots)):
            return _fail(why, "no function slots (%d pure)" % len(slots))
        return VtableInfo(address=ap, slots=slots, typeinfo_addr=td,
                          object_offset=offset, rtti_name=name,
                          bases=list(bases), unresolved=unresolved, vbases=list(vbases))

    def symbol_candidates(self):
        for sym in self.bv.get_symbols():
            if sym.raw_name.startswith("??_7") and sym.type == SymbolType.DataSymbol:
                yield sym.address, sym.address, sym.raw_name

    def symbol_class(self, raw):
        """Class of a vftable symbol: '??_7Dog@zoo@@6B@' -> 'zoo::Dog'."""
        end = raw.find("@@6B")
        if not raw.startswith("??_7") or end < 0:
            return None
        return demangle_name(self.bv, ".?AV" + raw[4:end] + "@@")

    def is_rtti_header_ref(self, val):
        """True when val points at a complete object locator."""
        if val in self._col_cache:
            return self._col_cache[val]
        ok = self.parse_col(val) is not None
        self._col_cache[val] = ok
        return ok

    def prime(self, ti_addrs):
        return None

    def typeinfo_addrs_of(self, candidates):
        return set()
