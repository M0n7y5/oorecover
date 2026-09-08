# OORecover

OORecover recovers C++ classes from a binary inside Binary Ninja. It finds vtables (symbols, Itanium and MSVC RTTI, pointer scans) and collects this-pointer facts from MLIL SSA: vtable installs, member accesses, constructor chains, allocations, argument passing. It writes the result back into the database: a struct per class with embedded bases and observed members, a VTable struct per table with typed slots, function names, signatures with a typed `this`, cross-references from virtual call sites to their implementations, and types on static instances. It records only what the binary proves. There is no guessing phase: every conclusion rests on a vtable store, a mangled name, a member access or an allocation, and contradictions are withdrawn before anything is applied. It runs on the analysed database, so what Binary Ninja already knows (its RTTI vtable types, user types, symbols) is kept and extended.

## Before and after

The fixture `tests/testprog.cpp` defines these two classes in `namespace zoo` (trimmed):

```cpp
class Animal {
public:
    Animal() { age = 0; tag = 1; }
    virtual ~Animal() { tag = -1; }
    virtual int speak() { return age; }
    virtual int legs() { return 4; }
    int rate(int k);
    int age;
    long tag;
};

class Dog : public Animal {
public:
    int speak() override { return age + tricks; }
    virtual void bark() { tricks++; }
    int tricks;
};
```

`tests/testprog_stripped` is that program built with `g++ -O1 -fno-inline -s`: RTTI present, no symbols, so Binary Ninja's own RTTI pass already names the vtables (`_vtable_for_zoo::Animal`, typed `struct zoo::Animal::VTable`) but every method is a `sub_` with auto-typed parameters. Pseudo C before and after the run, as `tests/reports/testprog_stripped.decompile.md` captures it:

`zoo::Animal::Animal()` before:
```c
int64_t sub_402982(struct zoo::Animal::VTable** arg1)
{
    *(uint64_t*)arg1 = &_vtable_for_zoo::Animal;
    arg1[1] = 0;
    arg1[2] = 1;
    return &_vtable_for_zoo::Animal;
}
```
after:
```c
int64_t zoo::Animal::ctor(struct zoo::Animal* this)
{
    *(uint192_t*)this = struct zoo::Animal {
        ._vftable = &_vtable_for_zoo::Animal,
        .m_8 = 0,
        .m_10 = 1
    };
    return &_vtable_for_zoo::Animal;
}
```
`zoo::Animal::rate(int)` before:
```c
uint64_t sub_4021dc(int64_t* arg1, int32_t arg2)
{
    return (uint64_t)((*(uint64_t*)(*(uint64_t*)arg1 + 0x10))() * arg2 + arg1[1]);
}
```
after:
```c
uint64_t zoo::Animal::method_4021dc(struct zoo::Animal* this, int32_t arg2)
{
    return (uint64_t)(this->_vftable->vfunc_2(this) * arg2 + this->m_8);
}
```
`zoo::Dog::speak()` before:
```c
uint64_t sub_40280a(void* arg1)
{
    return (uint64_t)(*(uint32_t*)((char*)arg1 + 8) + *(uint32_t*)((char*)arg1 + 0x18));
}
```
after:
```c
uint64_t zoo::Dog::vfunc_2(struct zoo::Dog* this)
{
    return (uint64_t)(this->_base_Animal.m_8 + this->m_18);
}
```

The struct behind those names, with the source members for reference:

```c
struct zoo::Animal {                    // width 24
    struct zoo::Animal::VTable* _vftable;  // 0
    uint32_t m_8;                          // 8   (age)
    uint64_t m_10;                         // 16  (tag)
};
```

`rate` has no vtable slot; it is named `method_4021dc` because every caller passes an `Animal` built at the call site and the body reads a member past the vtable pointer. The free function `zoo::feed(Animal* a, int n)` at `0x4022c7` stays `sub_4022c7` (nothing names it) but gets the signature `uint64_t(struct zoo::Animal* arg1, int32_t arg2)` from the objects its callers pass, and its two virtual calls are resolved and cross-referenced:

```
0x4022d5  zoo::Animal slot 2  -> zoo::Animal::vfunc_2, zoo::Cat::thunk_10_2, zoo::Bat::vfunc_2, zoo::Dog::vfunc_2
0x4022e1  zoo::Animal slot 3  -> zoo::Animal::vfunc_3
```

## Usage

- Install: clone into `~/.binaryninja/plugins/oorecover` and restart Binary Ninja (Python 3 plugin, `minimumsupportedversion` 4300 in `plugin.json`). Run `Plugins > OORecover > Recover C++ Classes` (PluginCommand `OORecover\Recover C++ Classes`); it is a cancellable background task with progress text `OORecover: ...`.
- Two passes. Pass 1 recovers and applies; functions whose signatures hid `this` now carry it, so call sites carry arguments. Pass 2 re-collects only the changed functions and their callers and reuses the other facts. Log lines (`oorecover` logger) to look for: `model: N classes, ...`, `applied N class types (...)`, `pass 2 done`, and finally `oorecover: N classes (itanium ABI)`.
- Time: the fixture binaries take seconds. On a 3 GB database with about 6900 classes the two passes take about 14 minutes, most of it Binary Ninja producing MLIL. A database typed by an earlier run reuses its facts and skips types and signatures that are already identical (`N types unchanged`, `N left as they were`). Each run is one undo action.
- What is written: struct types per class, `<Class>::VTable` struct types (secondary tables get `VTable_<offset>`, construction vtables `<Derived>::VTable_ctor_<Base>`), vtable data variables and symbols where Binary Ninja had none, function symbols for auto-named methods (`ctor`, `dtor`, `dtor_complete` for the Itanium complete destructor in the slot before the deleting `dtor`, `vfunc_N`, `thunk_<offset>_<slot>`, `method_<addr>`), user function types with `this`, user code references from virtual call sites, types on static instances, and two metadata keys: `oorecover.types` (types a run defined) and `oorecover.functions` (functions it named). Kept: existing user types not created by a previous run (logged `<name>: type exists, kept`), Binary Ninja's RTTI vtable types (updated in place under their names) and its symbols.

## What it recovers

- Vtables and RTTI: Itanium (`_ZTV`, `_ZTI`, VTT) and MSVC (`??_7`, `??_R`, complete object locators), with or without RTTI, with or without symbols; pointer-run scan for tables no symbol or header names.
- Classes and inheritance: bases at their offsets from RTTI or from the vtable group, virtual bases at the offsets the Itanium vtable header's vbase entries give (direct or inherited through an intermediate class; the one unexplained table when a class has a single virtual base, which covers MSVC), embedded objects built by the constructor, construction vtables (by `_ZTT` symbol or VTT shape) typed and attributed to the class under construction.
- Members and sizes: this-relative reads and writes in owned functions, object sizes from allocations and stack objects at construction sites, base tail padding reused as the Itanium layout does.
- Pointer members: a pointer-sized member every rooted store fills with an object of known class (built at an allocation or stack site, a static instance, `this`, or a parameter callers type) becomes `struct <common ancestor>*`; a store of a non-zero constant withdraws it. Virtual calls through such a member resolve to that class's slot and its overrides.
- Constructors and destructors: functions that store vtables through their own `this`; the derived-most table stored last marks a constructor, first a destructor; the other stores at the same offset name the bases.
- Classes without a vtable, from their mangled member functions (members, constructors, embedded bases); class names without RTTI, from the vtable symbol or from the constructor and destructor symbols that store each table.
- Virtual call resolution: calls through a vtable slot, including tail dispatch (`jmp [rax+slot]`), speculative devirtualisation guards, and calls through parameters of free functions and non-virtual members; resolved sites get user cross-references to every implementation, and pointer parameters get the class every caller passes.
- `this` typing: a `struct <Class>* this` on every owned function; detected by name, never by position, so 5.3 databases (explicit parameters only) and 6.0 databases (implicit `this` declared from the mangled name) are both handled.
- Struct returns through the hidden pointer: a native indirect return location with `this` in the following register and a `<Class>::<method>_result` placeholder sized from the writes, replaced by the real class when a constructor or a known callee names it.
- Namespace vs class: a scope is a class only with evidence (a vtable or recovered class, a structor or cv-qualified member, a signature mentioning it, a pre-existing struct type); otherwise its functions are namespace functions and a bogus leading `this` is removed.
- Non-virtual method naming on stripped binaries: `method_<addr>` under the class every caller passes an exact object of, when the body reads or writes a member of it.
- Consistency checks (OOAnalyzer's insanity rules): members past the object, a function claimed by unrelated classes (linker folding), inheritance cycles, structor roles that cannot all be true; the weaker conclusion is withdrawn, logged and reported under `findings`.

## Evidence rules

- A class exists when a vtable is installed through a `this` pointer, a mangled member name names it, or RTTI describes it. A pointer scan candidate that is never installed is dropped.
- A function is a member when it stores that class's vtable through its own `this`, sits in the class's primary table, carries a mangled member name, or (non-virtual, unnamed) is called with an exact object of the class by every caller and touches a member of it. A declared type alone is no evidence, and reads under a speculative devirtualisation guard belong to the inlined callee.
- A struct return is claimed only from a method's own facts: writes through a buffer in the first argument register with `this` in the next, a `this` handed to another class's constructor, or a namespace function reading one register more than its mangled name lists. The type of a slot's other implementations never makes a method a struct return, and unnamed functions with an auto signature are left alone.
- A placeholder result type is replaced only when the buffer is handed as `this` to a constructor known by symbol of a class at least as large as the writes, or forwarded as the hidden return of a callee whose result is known. A class of matching width is not a match; a buffer handed to an ordinary member call is only counted, since the callee may be a base member or a helper with an out pointer.

## Supported targets and limitations

- Targets: x86-64 and i386, SysV and MSVC calling conventions, Itanium and MSVC ABIs, ELF and PE. The fixtures are built with g++ and clang-cl.
- Classes with virtual bases report one size covering the virtual-base tail.
- A secondary table no base explains, because its class has several virtual bases and the vtable header could not be read (a virtual primary base puts vcall offsets in front of the vbase entries), is left unattributed (logged `table ... has no base there; ignored (N virtual bases, M tables unexplained)`). MSVC vbtables are not read: virtual base offsets there come only from the single-table case.
- Static Itanium members keep the `this` Binary Ninja 6.0 declares for them.
- A class known only through unrelated non-const members has no class evidence and is treated as a namespace.
- A method whose only buffer write is a copy of a member keeps its `_result` placeholder.
- Call sites with more than 32 candidate targets get a cross-reference to the static class's own slot only (`N sites capped`).
- A member is typed as a class pointer only from objects stored into it whole at a construction site or through `this`; pointers that arrive only through untyped globals or unknown callees stay `void*`.
- Functions discovered during pass 2 are not visited (`pass 2 done; N functions discovered late, not visited`).

## Development

| fixture (`tests/build.sh` builds them from `tests/testprog.cpp`; missing toolchains skip theirs) | covers |
|---|---|
| `testprog` | g++ -O1, RTTI and symbols: names from mangled symbols, `zoo::feed` typed from its name |
| `testprog_stripped` | same build stripped: names from RTTI only, `sub_` methods, `method_<addr>` naming |
| `testprog_nortti` | no RTTI, stripped: tables from installs and pointer scan, classes named `class_<vtable address>` |
| `testprog_o2` | -O2, no RTTI, stripped: inlining, speculative devirtualisation, tail dispatch |
| `testprog_nortti_sym` | no RTTI with symbols: class names from vtable symbols |
| `testprog_nortti_novt` | no RTTI, vtable symbols stripped: class names from constructor and destructor symbols |
| `testprog32` | i386 SysV, stripped: 4-byte pointers, stack arguments |
| `testprog_icf` | -O2 with lld `--icf=all`: identical functions of unrelated classes folded into one |
| `testprog_msvc64.exe` | clang-cl x64 with RTTI: MSVC vftables, complete object locators |
| `testprog_msvc32.exe` | clang-cl x86 with RTTI: 32-bit MSVC layout, absolute-pointer object locators |
| `testprog_msvc64_nortti.exe` | clang-cl x64 without RTTI or symbols: vftables back to back |

In-GUI runs: with Binary Ninja open, write the fixture paths one per line to `tests/autotest.txt`; the watcher thread started by `__init__.py` picks the file up within two seconds, hot-reloads the pipeline, runs each binary and writes `tests/reports/<fixture>.json`, `tests/reports/autotest.log` and `tests/reports/autotest.done`. A `#keep` line keeps the views open and `#trace 0xADDR` lines trace the collector on those functions instead of running the pipeline. `python3 tests/check_reports.py [fixture ...]` then asserts on the reports (default: every report present).

Offline tests, each runnable with plain `python3`: `tests/check_names.py` (undefined-name scan of the sources, which hot reload hides; no Binary Ninja needed), `tests/test_validate.py` (consistency rules on synthetic models) and `tests/test_demangle.py` (typeinfo and MSVC type name demangling). The last two import the plugin package, which imports `binaryninja`, so put the Binary Ninja Python API on `PYTHONPATH`.

Directives: `tests/trace.txt` with `0xADDR` words (plus `after-apply` to trace after a first recover-and-apply, `callers` to include callers) makes the next run trace those functions instead of recovering; `tests/decompile.txt` with `0xADDR [label]` lines makes it write each function's Pseudo C before and after the run to `tests/reports/<fixture>.decompile.md`; `tests/reanalyze.txt` makes it discard the saved analysis and reanalyse the whole binary first, to measure what a core upgrade changes. All three files are gitignored. A `tests/trace.txt` run still writes `tests/reports/<fixture>.json`, with the empty trace result: copy a report you want to keep before tracing.

## Binary Ninja 6.0 notes

6.0 declares an implicit `this` on every Itanium name with a nested scope when it types a function from its demangled symbol, namespace functions such as `zoo::feed(zoo::Animal*, int)` and static members included; thunk symbols and 5.3 databases keep the explicit list. The plugin therefore finds `this` by name, never by position. Struct returns use the native indirect return location (`ReturnValue` with `ValueLocation(..., indirect=True, returned_pointer=...)`), which Binary Ninja lays out in the following argument register (`rsi` on SysV x86-64, `rdx` on MSVC x64, the next stack slot on i386) and prints as `this @ rsi` and `*rdi -> *rax`. Demangling uses one `DemanglerConfig` per view whose `simplify` follows `analysis.types.templateSimplifier`, so class names are spelled the way Binary Ninja spells its own symbols and types.
