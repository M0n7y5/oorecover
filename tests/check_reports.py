"""Assert on the reports written by the in-GUI autotest run.

Usage: python3 check_reports.py [fixture ...]   (default: every report present)
"""
import json
import os
import re
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
REPORTS = os.path.join(HERE, "reports")

RTTI_FIXTURES = ("testprog", "testprog_stripped", "testprog32",
                 "testprog_msvc64.exe", "testprog_msvc32.exe")
NORTTI_FIXTURES = ("testprog_nortti", "testprog_o2", "testprog_msvc64_nortti.exe")
NAMED_NORTTI_FIXTURES = ("testprog_nortti_sym", "testprog_nortti_novt")
FOLDED_FIXTURES = ("testprog_icf",)
# Itanium fixtures with function symbols: zoo::feed is typed from its name.
SYMBOL_FIXTURES = ("testprog", "testprog_nortti_sym", "testprog_nortti_novt", "testprog_icf")


def load(name):
    with open(os.path.join(REPORTS, name + ".json")) as f:
        return json.load(f)


def layout(rep):
    """Field offsets per ABI and width. Itanium reuses a base's tail padding
    for derived members (echoloc lands right after Wing::span); MSVC does not."""
    p = rep["ptrsize"]
    itanium = rep["abi"] == "itanium"
    long_size = 8 if (p == 8 and itanium) else 4
    animal = p + 4 + long_size
    animal += (-animal) % p
    wing_dsize = p + 4
    wing = wing_dsize + (-wing_dsize) % p
    echoloc = animal + (wing_dsize if itanium else wing)
    return {"age": p, "animal": animal, "wing": wing,
            "tricks": animal, "wing_off": animal, "echoloc": echoloc}


def base_map(cls):
    return {b["name"]: b for b in cls["bases"]}


def member_names(cls):
    t = cls.get("type") or {}
    return {m[1]: m for m in (t.get("members") or [])}


def check_rtti(name):
    rep = load(name)
    check_coexistence(name, rep)
    lay = layout(rep)
    cmap = {c["name"]: c for c in rep["classes"]}
    for expected in ("zoo::Animal", "zoo::Dog", "zoo::Wing", "zoo::Bat",
                     "zoo::Shape", "zoo::Square", "zoo::Cat"):
        assert expected in cmap, "%s: missing %s; got %s" % (name, expected, sorted(cmap))

    if rep["abi"] == "itanium":
        assert [i["class"] for i in rep["instances"].values()] == ["zoo::Beacon"], (name, rep["instances"])
    animal, dog, bat = cmap["zoo::Animal"], cmap["zoo::Dog"], cmap["zoo::Bat"]
    assert base_map(dog).get("zoo::Animal", {}).get("offset") == 0, (name, dog["bases"])
    assert base_map(cmap["zoo::Square"]).get("zoo::Shape", {}).get("offset") == 0
    bb = base_map(bat)
    assert bb.get("zoo::Animal", {}).get("offset") == 0, (name, bat["bases"])
    assert bb.get("zoo::Wing", {}).get("offset") == lay["wing_off"], (name, bat["bases"], lay)
    cb = base_map(cmap["zoo::Cat"])
    assert cb.get("zoo::Animal", {}).get("virtual") is True, (name, cmap["zoo::Cat"]["bases"])
    assert sorted(int(k) for k in bat["vtables"]) == [0, lay["wing_off"]], (name, bat["vtables"])

    assert str(lay["age"]) in animal["members"], (name, animal["members"])
    assert animal["members"][str(lay["age"])][0] in (4, 8), (name, animal["members"])
    age_member = member_names(animal).get("m_%x" % lay["age"])
    assert age_member and age_member[2] == "uint32_t", (name, member_names(animal))
    assert str(lay["tricks"]) in dog["members"], (name, dog["members"])
    assert dog["size"] >= lay["animal"] + 4, (name, dog["size"])
    assert bat["size"] >= lay["echoloc"] + 4, (name, bat["size"])

    tm = member_names(dog)
    assert "_base_Animal" in tm and tm["_base_Animal"][0] == 0, (name, tm)
    assert "m_%x" % lay["tricks"] in tm, (name, tm)
    assert "_base_Wing" in member_names(bat), (name, member_names(bat))
    assert member_names(bat)["_base_Wing"][0] == lay["wing_off"]
    assert "_vftable" in member_names(animal), (name, member_names(animal))
    vt = dog["vtbl_types"]["0"]
    assert vt and len(vt["members"]) >= 4, (name, vt)

    for cls in rep["classes"]:
        for fn, info in cls["functions"].items():
            assert cls["name"] + "*" in info["type"] or fn in cls["thunks"], \
                (name, cls["name"], fn, info)
    if rep["abi"] == "itanium":
        assert None in cmap["zoo::Shape"]["vtables"]["0"]["slots"], \
            (name, "pure virtual slot not detected")
        if name != "testprog_o2":
            assert dog["ctors"], (name, "no Dog constructor")
    vcalls = rep.get("vcalls")
    if vcalls is not None:
        describe = [v for v in vcalls if v["class"] == "zoo::Animal" and not v["exact"]]
        assert describe, (name, "no virtual call resolved inside Animal::describe")
        speak_targets = max(describe, key=lambda v: len(v["targets"]))["targets"]
        assert len(speak_targets) >= 4, (name, "speak overrides not resolved", describe)
        if rep["abi"] == "itanium":
            exact = [v for v in vcalls if v["class"] == "zoo::Dog" and v["exact"]]
            assert exact and len(exact[0]["targets"]) == 1, (name, "heap->speak() not resolved exactly", exact)
        owned = {fn for c in rep["classes"] for fn in c["functions"]}
        free = [v for v in vcalls if v["caller"] not in owned and not v["exact"]]
        assert free, (name, "no virtual call resolved through a free function's parameter")
        use = max(free, key=lambda v: len(v["targets"]))
        assert use["class"] == "zoo::Animal" and len(use["targets"]) >= 4, (name, "use(Animal*) unresolved", free)
    # Animal::info returns a struct by value: the writes into the hidden
    # buffer must not become members of Animal, and the signature returns
    # through the hidden pointer with this as the first parameter.
    assert max(int(o) for o in animal["members"]) < lay["animal"], (name, "sret buffer taken for members", animal["members"])
    if name == "testprog":
        # info2 adds explicit parameters: a pinned location computed without
        # the hidden pointer once collided with this and left the signature
        # as (int32_t arg2 @ rsi, int32_t arg2 @ rsi, ...) with this gone.
        by_name = {f["name"]: f for f in animal["functions"].values()}
        for method, arity in (("_ZN3zoo6Animal4infoEv", 1), ("_ZN3zoo6Animal5info2Eil", 3)):
            found = by_name.get(method)
            assert found and "sret" not in found["type"], (name, method, found)
            assert "(struct zoo::Animal* this" in found["type"], (name, method, found)
            assert found["return_location"] and found["return_location"].startswith("*"), (name, method, found)
            inner = found["type"][found["type"].index("(") + 1:found["type"].rindex(")")]
            names = [p.split("@")[0].split()[-1] for p in inner.split(",")]
            assert len(names) == arity and len(names) == len(set(names)), (name, method, "parameter names", names)
        heap_calls = [v for v in vcalls if v["caller_name"] == "main" and v["class"] == "zoo::Dog" and v["exact"]]
        assert len(heap_calls) >= 2, (name, "heap->info2 not resolved", heap_calls)
        assert any(v["target_names"] == ["_ZN3zoo6Animal5info2Eil"] for v in heap_calls), (name, "heap->info2 target", heap_calls)
    if name == "testprog":
        beacon = cmap["zoo::Beacon"]
        assert beacon["embedded"] == {"16": "zoo::Stats"}, (name, "embedded Stats not found", beacon["embedded"])
        assert member_names(beacon).get("obj_10", [None, None, None])[2] == "struct zoo::Stats", (name, member_names(beacon))
        assert not beacon["bases"], (name, "embedded object mistaken for a base", beacon["bases"])
    if name == "testprog":
        stats = cmap.get("zoo::Stats")
        assert stats is not None and not stats["vtables"], (name, "vtable-less zoo::Stats not recovered", sorted(cmap))
        assert stats["ctors"] and len(stats["methods"]) == 1, (name, "Stats ctor/bump attribution", stats)
        assert all("zoo::Stats*" in f["type"] for f in stats["functions"].values()), (name, stats["functions"])
        sm = member_names(stats)
        assert "m_0" in sm and "m_4" in sm and "m_8" in sm and "_vftable" not in sm, (name, sm)
        assert stats["type"]["width"] >= 16, (name, stats["type"])
    if name == "testprog":
        # Non-virtual member with a demangled signature lacking this: only the
        # symbol-bearing fixture exercises this path (the others are stripped).
        rate = [v for v in vcalls if "rate" in (v["caller_name"] or "")]
        assert rate and len(rate[0]["targets"]) >= 4, (name, "Animal::rate's speak() unresolved", rate)
        rate_fn = [f for c in rep["classes"] for f in c["functions"].values() if "rate" in f["name"]]
        assert not rate_fn, (name, "Animal::rate is not virtual and must not be owned", rate_fn)
    if name == "testprog":
        legs = [f for f in animal["functions"].values() if "legs" in f["name"]]
        assert legs and "zoo::Animal*" in legs[0]["type"], (name, animal["functions"])
        assert not any("legs" in f["name"] for f in dog["functions"].values()), \
            (name, "Dog stole Animal::legs")


def check_coexistence(name, rep, allowed_findings=()):
    """Binary Ninja's own RTTI artifacts are absorbed, not duplicated: its
    symbols survive, every table ends up with one VTable type in its naming
    scheme, and none of its superseded VTable structs linger."""
    native, final = rep["native"], rep["final"]
    kept = {t["address"] for c in rep["classes"] for t in c["vtables"].values()}
    for addr, before in native["tables"].items():
        if addr not in kept:
            continue   # a scanned candidate the model rejected keeps whatever it had
        after = final["tables"][addr]
        if before["symbol"]:
            assert after["symbol"] == before["symbol"], (name, addr, before, after)
        else:
            assert after["symbol"] and ("_vtable_for_" in after["symbol"]
                                        or "`vftable'" in after["symbol"]), (name, addr, after)
        assert after["type"] and "::VTable" in after["type"], (name, addr, after)
        assert "::vtbl" not in after["type"], (name, addr, after)
    native_types = [t["type"] for t in native["tables"].values()]
    for addr, before in native["tables"].items():
        if before["type"] and "::VTable" in before["type"] and native_types.count(before["type"]) == 1:
            assert final["tables"][addr]["type"] == before["type"], (name, addr, before, final["tables"][addr])
    types = final["vtable_types"]
    assert len(types) == len(set(types)), (name, "duplicate VTable types", types)
    lost = rep.get("lost_vcalls", [])
    assert not lost, (name, "virtual calls resolved in pass 1 vanished after applying types", lost[:3])
    findings = [f for f in rep.get("findings", []) if f["kind"] not in allowed_findings]
    assert not findings, (name, "model contradictions", findings[:3])
    # The static g_beacon: its constructor runs at startup and stores the
    # vtable into a fixed address, which types the variable there.
    instances = rep.get("instances", {})
    if rep["abi"] == "itanium":
        # The CRT-less MSVC fixtures never run their dynamic initialisers, so
        # nothing there constructs g_beacon.
        assert instances, (name, "static instance not found")
    for addr, i in instances.items():
        assert i["class"] in i["type"], (name, "static instance not typed", addr, i)
    applied = {t["type"].replace("struct ", "") for t in final["tables"].values()}
    stray = [t for t in types if t not in applied]
    assert not stray, (name, "VTable types not on any table", stray)


def check_namespaces(name, rep):
    """A namespace is not a class: no report has a class named zoo (or any
    scope another class nests in), and the free function zoo::feed keeps
    exactly the parameters its mangled name lists, no this."""
    names = [c["name"] for c in rep["classes"]]
    scopes = [n for n in names if any(o.startswith(n + "::") for o in names)]
    assert "zoo" not in names and not scopes, (name, "namespace taken for a class", scopes or names)
    if name not in SYMBOL_FIXTURES:
        return
    feed = [v for v in rep["vcalls"] if v["caller_name"] == "_ZN3zoo4feedEPNS_6AnimalEi"]
    assert feed, (name, "zoo::feed's virtual calls unresolved")
    for v in feed:
        assert v["class"] == "zoo::Animal", (name, "zoo::feed call not through Animal*", v)
        params = v["caller_type"].split("(", 1)[1]
        assert re.fullmatch(r"(struct )?zoo::Animal\* \w+, int32_t \w+\)", params), \
            (name, "zoo::feed signature", v["caller_type"])
    # zoo::Counter has no evidence but arity: bump reads a third argument
    # register for its two explicit parameters, so it keeps its this.
    bump = [v for v in rep["vcalls"] if v["caller_name"] == "_ZN3zoo7Counter4bumpEiPNS_6AnimalE"]
    assert bump, (name, "zoo::Counter::bump's virtual call unresolved")
    for v in bump:
        assert v["class"] == "zoo::Animal", (name, "Counter::bump call not through Animal*", v)
        assert "zoo::Counter* this" in v["caller_type"], (name, "Counter::bump lost its this", v["caller_type"])


STRUCT_RETURNS = {"_ZN3zoo6Animal5labelEv": "struct zoo::Label(",       # built in the buffer by Label's constructor
                  "_ZN3zoo3Dog5labelEv": "struct zoo::Label(",          # same slot, same type
                  "_ZN3zoo5Puppy3posEv": "struct zoo::Puppy::pos_result("}   # copy only: placeholder kept
# label2 forwards its buffer to label() on another object. The call carries
# no MLIL parameters (rdi is passed through untouched) and its only caller
# is virtual, so no fact names the object: the signature stays Binary
# Ninja's own, never a wrong one.
FORWARD_UNTYPED = ("_ZN3zoo6Animal6label2Ev", "struct zoo::Animal*(")
# -O2 inlines Label's constructor, so every label writes the buffer itself
# and nothing names the type: placeholders, one per slot.
STRUCT_RETURNS_INLINED = {"_ZN3zoo6Animal5labelEv": "struct zoo::Animal::label_result(",
                          "_ZN3zoo3Dog5labelEv": "struct zoo::Dog::label_result(",
                          "_ZN3zoo5Puppy3posEv": "struct zoo::Puppy::pos_result("}


def check_struct_returns(name, rep):
    """Methods returning a struct by value carry the hidden-pointer return
    location; the buffer names the result type when a constructor builds
    it or when it is forwarded to a method whose result is known."""
    if name not in SYMBOL_FIXTURES:
        return
    funcs = {v["name"]: v for c in rep["classes"] for v in c["functions"].values()}
    expected = STRUCT_RETURNS_INLINED if name in FOLDED_FIXTURES else STRUCT_RETURNS
    f = funcs.get(FORWARD_UNTYPED[0])
    assert f is not None and f["type"].startswith(FORWARD_UNTYPED[1]), (name, "label2", f)
    for sym, prefix in expected.items():
        f = funcs.get(sym)
        assert f is not None, (name, "struct-returning method not owned", sym)
        assert f["type"].startswith(prefix), (name, sym, "return type", f["type"])
        assert f["return_location"] and "*" in f["return_location"], (name, sym, f["return_location"])
    # zoo::where returns a Vec through the hidden buffer in the first register;
    # the namespace function keeps no this and its parameters follow the buffer.
    where = [v for v in rep["vcalls"] if v["caller_name"] == "_ZN3zoo5whereEPNS_6AnimalEi"]
    assert where, (name, "zoo::where's virtual call unresolved")
    for v in where:
        assert v["class"] == "zoo::Animal" and "_ZN3zoo6Animal4legsEv" in v["target_names"], (name, "zoo::where site", v)
        assert re.fullmatch(r"struct zoo::where_result\(struct zoo::Animal\* \w+ @ rsi, int32_t \w+ @ rdx\)",
                            v["caller_type"]), (name, "zoo::where signature", v["caller_type"])
    assert not any(f["kind"] == "slot returns two types" for f in rep["findings"]), (name, rep["findings"])


def check_construction(name, rep):
    """Lion derives from Cat, which has Animal as a virtual base, so g++
    emits a construction vtable for Cat-in-Lion: laid out like Cat's tables
    and carrying Cat's typeinfo, it must neither pass for Cat's own table
    nor found a class, and it is recorded on Cat under Lion's name."""
    if rep["abi"] != "itanium":
        return
    cmap = {c["name"]: c for c in rep["classes"]}
    by_addr = {t["address"]: c["name"] for c in rep["classes"] for t in c["vtables"].values()}
    if name in NORTTI_FIXTURES or name in NAMED_NORTTI_FIXTURES:
        # Without typeinfo the construction vtable's tables are provisional
        # and dropped (nothing in code installs them directly), so no class
        # can come from them; Lion's bases then read from its inlined
        # constructors, as for every class of these fixtures.
        assert not any(c["name"].startswith("class_") for c in rep["classes"]) or name in NORTTI_FIXTURES, \
            (name, [c["name"] for c in rep["classes"]])
        return
    lion, cat = cmap.get("zoo::Lion"), cmap.get("zoo::Cat")
    assert lion is not None and cat is not None, (name, "Lion or Cat missing", sorted(cmap))
    assert base_map(lion).get("zoo::Cat", {}).get("offset") == 0, (name, lion["bases"])
    assert base_map(cat).get("zoo::Animal", {}).get("virtual") is True, (name, cat["bases"])
    ctor = cat["construction_vtables"].get("zoo::Lion")
    assert ctor and "0" in ctor, (name, "construction vtable for Cat-in-Lion not recorded", cat["construction_vtables"])
    for addr in ctor.values():
        assert addr not in by_addr, (name, "construction vtable claimed as a class table", addr, by_addr[addr])
        final = rep["final"]["tables"].get(addr)
        assert final and final["type"] and "zoo::Cat::VTable" in final["type"], (name, addr, final)
    assert len(cat["vtables"]) == 2, (name, "Cat's own tables", cat["vtables"])


# Non-virtual members by address on the stripped copy of testprog (same
# code layout), from testprog.json: Animal::rate reads age through its
# object, Kennel::noise reads pet; Puppy::play and rest only call virtuals,
# as use() does, so they stay unnamed; Stats and Counter exist only by symbol here.
NONVIRTUAL = {"testprog_stripped": {"0x4021dc": "zoo::Animal", "0x402c0c": "zoo::Kennel"},
              "testprog32": {"0x1120e": "zoo::Animal", "0x11de0": "zoo::Kennel"},
              "testprog_msvc64.exe": {"0x140001004": "zoo::Animal", "0x1400016a2": "zoo::Kennel"},
              "testprog_msvc32.exe": {"0x401004": "zoo::Animal", "0x401580": "zoo::Kennel"}}
# use, measure, flapit, labels, zoo::feed, zoo::where, zoo::poke.
FREE_FUNCTIONS = {"testprog_stripped": ("0x40226a", "0x402294", "0x4022a3", "0x40232f", "0x4022c7", "0x4022ed", "0x402321"),
                  "testprog32": ("0x112a8", "0x112cb", "0x112dc", "0x1136f", "0x1130a", "0x11330", "0x1135f"),
                  # -O2: speculative devirtualisation inlines callee bodies under
                  # type guards, so every function reading members through its
                  # parameter is guarded, Animal::rate and Kennel::noise included:
                  # nothing is named.
                  "testprog_o2": ("0x402770", "0x4027b0", "0x4027e0", "0x4028e0", "0x402820", "0x402860",
                                  "0x4028b0", "0x402660", "0x402630")}


def check_nonvirtual(name, rep):
    """Unnamed functions every caller hands an object of one class, some
    of them exact, and that read a member of it are that class's methods:
    named method_<address>, typed with this, listed under the class. Free
    functions taking the object (use, measure, flapit, labels, zoo::feed,
    zoo::where) are not."""
    if name not in NONVIRTUAL and name not in FREE_FUNCTIONS:
        return
    cmap = {c["name"]: c for c in rep["classes"]}
    claimed = {fn: c["name"] for c in rep["classes"] for fn in c["nonvirtual"]}
    for fn, cls in NONVIRTUAL.get(name, {}).items():
        assert claimed.get(fn) == cls, (name, fn, "expected under", cls, "got", claimed.get(fn))
        f = cmap[cls]["functions"][fn]
        assert f["name"] == "%s::method_%s" % (cls, fn[2:]), (name, f["name"])
        assert f["type"].split("(", 1)[1].startswith("struct %s* this" % cls), (name, f["type"])
    for fn in FREE_FUNCTIONS.get(name, ()):
        assert fn not in claimed, (name, "free function claimed", fn, claimed[fn])
    assert not (set(claimed) - set(NONVIRTUAL.get(name, {}))), (name, "unexpected attributions", claimed)


def check_puppy(name, rep):
    """Puppy::play reads its vtable through _base_Dog._base_Animal and calls
    fetch (slot 9, past Animal's and Dog's VTable) and kind; at -O2 gcc
    guards each with a compare against the expected function and reloads
    the vtable on the indirect branch. Puppy::rest is a tail dispatch
    (jmp [rax+slot]). Every site resolves in the final pass and the guards
    add none; nothing is lost between passes."""
    assert not rep["lost_vcalls"], (name, "virtual calls lost between passes", rep["lost_vcalls"])
    if name in SYMBOL_FIXTURES:
        by_caller = {}
        for v in rep["vcalls"]:
            by_caller.setdefault(v["caller_name"], []).append(v)
        rest = by_caller.get("_ZN3zoo5Puppy4restEv", [])
        assert [v["target_names"] for v in rest] == [["_ZN3zoo5Puppy5fetchEv"]], \
            (name, "Puppy::rest tail dispatch", rest)
        play = by_caller.get("_ZN3zoo5Puppy4playEv", [])
        targets = [t for v in play for t in v["target_names"]]
        assert len(play) == 2 and "_ZN3zoo5Puppy5fetchEv" in targets and any(t.endswith("4kindEv") for t in targets), \
            (name, "Puppy::play sites", play)
        return
    # Without symbols: fetch and kind are the slots before pos, the last of
    # the longest table; play and rest both reach fetch, play reaches kind.
    longest = max((t for c in rep["classes"] for t in c["vtables"].values()), key=lambda t: len(t["slots"]))
    fetch = [v for v in rep["vcalls"] if v["targets"] == [longest["slots"][-2]]]
    kind = [v for v in rep["vcalls"] if v["targets"] == [longest["slots"][-3]]]
    assert len(fetch) >= 2 and len(kind) >= 1, (name, "Puppy::play and rest sites to the last slots", fetch, kind)


def check_kennel(name, rep):
    """Kennel's constructor stores the Dog it builds into pet, at offset
    ptrsize: the only class-pointer member in the fixture, typed with Dog
    (by name wherever Dog has one, and always the class built at an
    allocation site inside Kennel's constructor), and noise()'s call
    through it resolves to Dog's speak slot, not exactly (pet may hold a
    Puppy). The struct member reads struct Dog*. The MSVC fixtures inline
    their own operator new, so no allocation roots an object there and
    pet stays untyped; -O2 (testprog_o2, testprog_icf) knows pet holds a
    Dog and devirtualises noise(), so only the destructor's delete calls
    through the member there."""
    p = rep["ptrsize"]
    cmap = {c["name"]: c for c in rep["classes"]}
    typed = [(c, off, m) for c in rep["classes"] for off, m in c["members"].items() if len(m) > 4]
    if not any(s.endswith(" alloc") for c in rep["classes"] for s in c["site_functions"]):
        assert not typed, (name, "class-pointer member without an allocation", typed)
        return
    assert len(typed) == 1, (name, "one class-pointer member expected", [(c["name"], off, m) for c, off, m in typed])
    kennel, off, m = typed[0]
    assert int(off) == p and m[0] == p, (name, "pet at offset ptrsize", off, m)
    dog = cmap.get(m[4])
    assert dog is not None, (name, "pointee class missing", m)
    if "zoo::Dog" in cmap:
        assert m[4] == "zoo::Dog" and kennel["name"] == "zoo::Kennel", (name, kennel["name"], m)
    assert any(fn in kennel["ctors"] and kind == "alloc" for fn, kind in (s.split() for s in dog["site_functions"])), \
        (name, "pet's Dog not built in Kennel's constructor", kennel["ctors"], dog["site_functions"])
    assert member_names(kennel).get("m_%x" % p, [None] * 3)[2] == "struct %s*" % m[4], (name, member_names(kennel))
    if name in ("testprog_o2",) + FOLDED_FIXTURES:
        noise = [v for v in rep["vcalls"] if v["class"] == dog["name"] and not v["exact"]]
        assert any(v["caller"] in kennel["dtors"] for v in noise), (name, "~Kennel's delete pet unresolved", noise)
        return
    speak = dog["vtables"]["0"]["slots"][2 if rep["abi"] == "itanium" else 1]
    noise = [v for v in rep["vcalls"] if v["class"] == dog["name"] and not v["exact"]]
    assert any(v["targets"] == [speak] for v in noise), (name, "noise()'s pet->speak() unresolved", speak, noise)
    if name in SYMBOL_FIXTURES:
        assert any(v["caller_name"] == "_ZN3zoo6Kennel5noiseEv" and v["target_names"] == ["_ZN3zoo3Dog5speakEv"]
                   for v in noise), (name, "Kennel::noise site", noise)


INLINED_CTORS = ("testprog_o2", "testprog_msvc64_nortti.exe")


def check_nortti(name):
    rep = load(name)
    check_coexistence(name, rep)
    classes = rep["classes"]
    inlined = name in INLINED_CTORS
    # Header-less tables (MSVC without RTTI) sit back to back; the split at
    # referenced slots must keep them apart: Puppy's table is the longest at 13.
    assert max(len(t["slots"]) for c in classes for t in c["vtables"].values()) <= 13, \
        (name, "tables merged", [(c["name"], len(t["slots"])) for c in classes for t in c["vtables"].values()])
    assert not any(not c["vtables"] for c in classes), (name, "plain class in a stripped binary", [c["name"] for c in classes if not c["vtables"]])
    assert len(classes) >= 5, (name, [c["name"] for c in classes])
    assert all(c["name"].startswith("class_") for c in classes), (name, [c["name"] for c in classes])
    assert any(len(c["vtables"]) >= 2 for c in classes) or inlined, (name, "no multi-vtable class")
    if not inlined:
        assert any(c["bases"] for c in classes), (name, "no inferred bases")
    assert any(c["ctors"] or c["dtors"] for c in classes), (name, "no ctors or dtors")
    assert any(c["size"] >= 24 for c in classes), (name, [c["size"] for c in classes])
    for cls in classes:
        assert cls["type"] is not None, (name, cls["name"], "type not applied")
    owned = {fn for c in classes for fn in c["functions"]}
    free = [v for v in rep.get("vcalls", []) if v["caller"] not in owned and not v["exact"]]
    assert free, (name, "no virtual call resolved through an inferred parameter class")
    if not inlined:
        assert max(len(v["targets"]) for v in free) >= 4, (name, "use(Animal*) unresolved", free)


def check_nortti_named(name):
    """No RTTI, but symbols: the classes carry their real names, from their
    vtable symbol (nortti_sym) or from their constructors (nortti_novt).
    Base offsets come from the inlined base constructors, so a virtual base
    reads as a plain base at the offset the constructor used."""
    rep = load(name)
    check_coexistence(name, rep)
    lay = layout(rep)
    cmap = {c["name"]: c for c in rep["classes"]}
    for expected in ("zoo::Animal", "zoo::Dog", "zoo::Wing", "zoo::Bat",
                     "zoo::Shape", "zoo::Square", "zoo::Cat", "zoo::Stats"):
        assert expected in cmap, "%s: missing %s; got %s" % (name, expected, sorted(cmap))
    animal, dog, bat = cmap["zoo::Animal"], cmap["zoo::Dog"], cmap["zoo::Bat"]
    assert base_map(dog).get("zoo::Animal", {}).get("offset") == 0, (name, dog["bases"])
    assert base_map(cmap["zoo::Square"]).get("zoo::Shape", {}).get("offset") == 0, \
        (name, cmap["zoo::Square"]["bases"])
    assert base_map(bat).get("zoo::Wing", {}).get("offset") == lay["wing_off"], (name, bat["bases"])
    assert "zoo::Animal" in base_map(cmap["zoo::Cat"]), (name, cmap["zoo::Cat"]["bases"])
    assert sorted(int(k) for k in bat["vtables"]) == [0, lay["wing_off"]], (name, bat["vtables"])

    assert member_names(animal).get("m_%x" % lay["age"], [0, 0, 0])[2] == "uint32_t", \
        (name, member_names(animal))
    assert "_vftable" in member_names(animal), (name, member_names(animal))
    assert member_names(dog).get("_base_Animal", [None])[0] == 0, (name, member_names(dog))
    assert dog["size"] >= lay["animal"] + 4, (name, dog["size"])
    stats = cmap["zoo::Stats"]
    assert not stats["vtables"] and len(member_names(stats)) == 3, (name, stats)
    beacon = cmap["zoo::Beacon"]
    assert beacon["embedded"] == {"16": "zoo::Stats"} and not beacon["bases"], (name, beacon["embedded"], beacon["bases"])
    for cls in rep["classes"]:
        for fn, info in cls["functions"].items():
            assert cls["name"] + "*" in info["type"] or fn in cls["thunks"], \
                (name, cls["name"], fn, info)

    vcalls = rep["vcalls"]
    inside = [v for v in vcalls if v["class"] == "zoo::Animal" and not v["exact"]]
    assert max(len(v["targets"]) for v in inside) >= 4, (name, "speak overrides unresolved", inside)
    owned = {fn for c in rep["classes"] for fn in c["functions"]}
    free = [v for v in vcalls if v["caller"] not in owned and not v["exact"]]
    assert max(len(v["targets"]) for v in free) >= 4, (name, "use(Animal*) unresolved", free)
    exact = [v for v in vcalls if v["class"] == "zoo::Dog" and v["exact"]]
    assert exact and len(exact[0]["targets"]) == 1, (name, "heap->speak() not exact", exact)
    rate = [v for v in vcalls if "rate" in (v["caller_name"] or "")]
    assert rate and len(rate[0]["targets"]) >= 4, (name, "Animal::rate's speak() unresolved", rate)

    shape = cmap["zoo::Shape"]
    if name == "testprog_nortti_sym":
        # An abstract class's table holds null destructor slots and a pure
        # slot; only its symbol proves it is a table at all.
        assert shape["vtables"], (name, "abstract class table not found by symbol")
        assert all(s is None for s in shape["vtables"]["0"]["slots"]), (name, shape["vtables"])
    else:
        assert not shape["vtables"], (name, "table without a symbol or an install", shape)


def check_folded(name):
    """The linker folded Dog::kind with Cat::kind and Wing::tag with
    Square::tag. One function listed by unrelated classes belongs to their
    common base when there is one (Animal), and to nobody otherwise: it must
    not be typed or named after whichever class's symbol survived."""
    rep = load(name)
    check_coexistence(name, rep, allowed_findings=("folded into unrelated classes",))
    cmap = {c["name"]: c for c in rep["classes"]}
    for expected in ("zoo::Animal", "zoo::Dog", "zoo::Cat", "zoo::Wing", "zoo::Square"):
        assert expected in cmap, "%s: missing %s; got %s" % (name, expected, sorted(cmap))
    animal = cmap["zoo::Animal"]
    kinds = [fn for fn in animal["shared"] if "kind" in animal["functions"][fn]["name"]]
    assert len(kinds) == 1, (name, "folded kind() not shared under Animal", animal["shared"])
    kind = kinds[0]
    assert "zoo::Animal* this" in animal["functions"][kind]["type"], (name, animal["functions"][kind])
    for owner in ("zoo::Dog", "zoo::Cat"):
        assert kind not in cmap[owner]["functions"], (name, owner, "claims the folded kind()")
        assert kind in cmap[owner]["vtables"]["0"]["slots"], (name, owner, "table lost kind()")
    unowned = rep["unowned"]
    tags = [fn for fn, info in unowned.items() if "tag" in info["name"]]
    assert len(tags) == 1, (name, "folded tag() not unowned", unowned)
    tag = tags[0]
    for fn, info in unowned.items():
        assert "zoo::" not in info["type"], (name, "unowned function typed with a class", info)
    for cls in rep["classes"]:
        for fn in unowned:
            assert fn not in cls["functions"], (name, cls["name"], "claims an unowned function", fn)
    for owner in ("zoo::Wing", "zoo::Square"):
        assert tag in cmap[owner]["vtables"]["0"]["slots"], (name, owner, "table lost tag()")
    # The folded destructors: every class keeps exactly the destructor that
    # is its own or shared with relatives only.
    for cls in rep["classes"]:
        for fn in cls["dtors"]:
            assert cls["name"] + "* this" in cls["functions"][fn]["type"], (name, cls["name"], cls["functions"][fn])


def check_complete_dtors(name, rep):
    """Itanium keeps the complete destructor (D1) in the slot before the
    deleting one (D0). The model finds D0 from its operator delete call; the
    slot before it is D1 and gets named dtor_complete, listed under dtors.
    Symbol builds keep their mangled names. MSVC has one destructor slot."""
    if rep["abi"] != "itanium":
        return
    symbols = name in SYMBOL_FIXTURES
    pairs = []

    def deleting(cls, slots, i):
        """Slot i holds the class's deleting destructor: a D0 symbol, or an
        auto-named dtor that is not the first of a dtor/dtor_1 pair (both
        destructors found by the model, D1 first)."""
        fn = slots[i]
        if fn is None or fn not in cls["dtors"] or fn in cls["thunks"]:
            return False
        n = cls["functions"][fn]["name"]
        if symbols:
            return bool(re.fullmatch(r"_ZN.*D0Ev", n))
        if n != cls["name"] + "::dtor":
            return False
        nxt = slots[i + 1] if i + 1 < len(slots) else None
        return not (nxt in cls["dtors"] and cls["functions"][nxt]["name"] == cls["name"] + "::dtor_1")

    for cls in rep["classes"]:
        slots = cls["vtables"].get("0", {}).get("slots", [])
        for i, fn in enumerate(slots):
            info = cls["functions"].get(fn)
            if info is not None and info["name"].endswith("::dtor_complete"):
                assert i + 1 < len(slots) and deleting(cls, slots, i + 1), \
                    (name, cls["name"], "dtor_complete not followed by the deleting destructor", i, slots[i:i + 2])
                assert info["name"] == cls["name"] + "::dtor_complete" and fn in cls["dtors"], (name, cls["name"], info)
            if i == 0 or not deleting(cls, slots, i):
                continue
            d1 = slots[i - 1]
            if d1 not in cls["functions"] or d1 == fn or d1 in cls["thunks"]:
                continue
            pairs.append((cls, d1, fn))
            assert d1 in cls["dtors"], (name, cls["name"], "complete destructor not listed", d1, cls["dtors"])
            n1 = cls["functions"][d1]["name"]
            if symbols:
                assert re.fullmatch(r"_ZN.*D[12]Ev", n1), (name, cls["name"], n1)
            else:
                assert n1 == cls["name"] + "::dtor_complete", (name, cls["name"], n1)
    assert pairs, (name, "no destructor pair found")
    cmap = {c["name"]: c for c in rep["classes"]}
    if "zoo::Animal" in cmap:
        animal = cmap["zoo::Animal"]
    elif name in INLINED_CTORS:
        return   # -O2 devirtualises use(Animal*): nothing singles Animal out
    else:
        # Animal's table is the one use(Animal*) dispatches through.
        animal = cmap[max(rep["vcalls"], key=lambda v: len(v["targets"]))["class"]]
    slots = animal["vtables"]["0"]["slots"]
    d1, d0 = slots[0], slots[1]
    assert d0 in animal["dtors"], (name, animal["name"], animal["dtors"])
    if d1 not in animal["functions"]:
        # The linker folded the empty ~Animal() with unrelated destructors
        # (testprog_icf): it is nobody's, so it must not be claimed as Animal's.
        assert name in FOLDED_FIXTURES and d1 not in animal["dtors"], (name, animal["name"], d1, animal["dtors"])
        return
    assert d1 in animal["dtors"], (name, animal["name"], "complete destructor not listed", d1, animal["dtors"])
    n1, n0 = animal["functions"][d1]["name"], animal["functions"][d0]["name"]
    if symbols:
        assert (n1, n0) == ("_ZN3zoo6AnimalD1Ev", "_ZN3zoo6AnimalD0Ev"), (name, n1, n0)
        return
    assert (n1, n0) == (animal["name"] + "::dtor_complete", animal["name"] + "::dtor"), (name, n1, n0)
    members = animal["vtbl_types"]["0"]["members"]
    assert [m[1] for m in members[:2]] == ["dtor_complete", "dtor"], (name, members[:2])


def log_section(name):
    """Lines the autotest run logged for one fixture, [] without a log."""
    try:
        with open(os.path.join(REPORTS, "autotest.log")) as f:
            lines = f.read().split("\n")
    except FileNotFoundError:
        return []
    out, inside = [], False
    for line in lines:
        if line.startswith("=== "):
            inside = line[4:].strip() == name
        elif inside:
            out.append(line)
    return out


def check_virtual_base(name, rep):
    """Lion inherits Cat's virtual base Animal, which Lion's own RTTI never
    lists, yet Lion's vtable group carries a secondary table for the Animal
    sub-object. The vbase offset in Lion's primary table header (Itanium) or
    the one table no non-virtual base explains (MSVC) attributes it: Lion
    gains Animal as a virtual base at that offset, the table is Lion's,
    its overrides' thunks belong to Lion typed with Animal's this, its
    slots are typed, and calls through an Animal* reach Lion's overrides.
    Cat's own virtual base gets the offset of its own secondary table."""
    if name not in RTTI_FIXTURES:
        return
    itanium = rep["abi"] == "itanium"
    p = rep["ptrsize"]
    cmap = {c["name"]: c for c in rep["classes"]}
    lion, cat, animal = cmap["zoo::Lion"], cmap["zoo::Cat"], cmap["zoo::Animal"]
    cat_animal = base_map(cat)["zoo::Animal"]
    cat_off = cat_animal["offset"]
    assert cat_animal["virtual"] and cat_off is not None, (name, cat["bases"])
    assert sorted(int(o) for o in cat["vtables"]) == [0, cat_off], (name, cat["vtables"], cat_off)
    lb = base_map(lion)
    assert lb["zoo::Cat"] == {"name": "zoo::Cat", "offset": 0, "virtual": False}, (name, lion["bases"])
    assert "zoo::Animal" in lb and lb["zoo::Animal"]["virtual"] is True, (name, lion["bases"])
    off = lb["zoo::Animal"]["offset"]
    if itanium:
        # vptr, lives, then mane: it fits Cat's tail padding on x86-64 only.
        assert off == {8: 16, 4: 12}[p], (name, lion["bases"])
    else:
        assert off > cat_off, (name, lion["bases"], cat_off)
    assert sorted(int(o) for o in lion["vtables"]) == [0, off], (name, lion["vtables"], off)
    table = lion["vtables"][str(off)]
    assert len(table["slots"]) == len(animal["vtables"]["0"]["slots"]), (name, table, animal["vtables"]["0"])
    typed = lion["vtbl_types"][str(off)]
    assert typed and len(typed["members"]) == len(table["slots"]), (name, off, typed)
    thunks = [fn for fn in table["slots"] if fn in lion["thunks"]]
    assert len(thunks) >= 3 and all(lion["thunks"][fn] == off for fn in thunks), (name, table, lion["thunks"])
    for fn in thunks:
        assert "zoo::Animal*" in lion["functions"][fn]["type"], (name, fn, lion["functions"][fn])
    inherited = [fn for fn in table["slots"] if fn in animal["methods"]]
    assert inherited, (name, "Animal's own slots not left to Animal", table)
    assert not any(fn in lion["methods"] or fn in lion["dtors"] for fn in inherited), (name, table, lion["methods"])
    # use(&lion): legs() through an Animal* reaches Lion::legs by its thunk.
    resolved = [v for v in rep["vcalls"] if v["class"] == "zoo::Animal" and not v["exact"]
                and any(t in thunks for t in v["targets"])]
    assert len(resolved) >= 2, (name, "Lion's overrides missing from Animal* calls",
                                [v["targets"] for v in rep["vcalls"] if v["class"] == "zoo::Animal"])
    stray = [line for line in log_section(name) if "zoo::Lion:" in line and "has no base there" in line]
    assert not stray, (name, stray)


# Fixtures where Trunk's vtable is not in the binary: g++ at -O2 inlines
# its constructor away, lld-link drops clang-cl's unreferenced comdats.
BRIDGED_FIXTURES = ("testprog_icf", "testprog_msvc64.exe", "testprog_msvc32.exe")


def check_trunk(name, rep):
    """Elephant derives from Trunk (Horn at 0, Mixin past it), whose own
    vtable may be absent: Elephant's table for the Mixin sub-object is then
    explained only by Trunk's RTTI. Trunk becomes a class without tables
    carrying its bases, Elephant keeps Trunk as its base, and the table is
    Elephant's, typed for the Mixin sub-object."""
    if name not in RTTI_FIXTURES + FOLDED_FIXTURES:
        return
    p = rep["ptrsize"]
    cmap = {c["name"]: c for c in rep["classes"]}
    elephant, trunk = cmap["zoo::Elephant"], cmap["zoo::Trunk"]
    mixin_off = 2 * p    # Horn is a vptr and an int, padded to the pointer size
    assert elephant["bases"] == [{"name": "zoo::Trunk", "offset": 0, "virtual": False}], (name, elephant["bases"])
    tb = base_map(trunk)
    assert tb.get("zoo::Horn", {}).get("offset") == 0 and tb.get("zoo::Mixin", {}).get("offset") == mixin_off, (name, trunk["bases"])
    assert sorted(int(o) for o in elephant["vtables"]) == [0, mixin_off], (name, elephant["vtables"])
    typed = elephant["vtbl_types"][str(mixin_off)]
    assert typed and len(typed["members"]) == len(elephant["vtables"][str(mixin_off)]["slots"]), (name, typed)
    # Binary Ninja's own name for the table is kept when it has one, so only
    # the class is fixed: zoo::Mixin::zoo::Elephant::VTable or its spelling.
    final = rep["final"]["tables"][elephant["vtables"][str(mixin_off)]["address"]]
    assert final["type"] and "zoo::Elephant::VTable" in final["type"], (name, final)
    thunks = [fn for fn in elephant["vtables"][str(mixin_off)]["slots"] if fn in elephant["thunks"]]
    assert thunks and all(elephant["thunks"][fn] == mixin_off for fn in thunks), (name, elephant["thunks"])
    if name in BRIDGED_FIXTURES:
        assert not trunk["vtables"] and not trunk["functions"], (name, "Trunk has a vtable after all", trunk["vtables"])
        assert any("carry bases with one" in line for line in log_section(name)), (name, "no bridged class logged")
    else:
        assert sorted(int(o) for o in trunk["vtables"]) == [0, mixin_off], (name, trunk["vtables"])
    stray = [line for line in log_section(name) if "has no base there" in line]
    assert not stray, (name, stray)


def main(argv):
    names = argv or [n for n in RTTI_FIXTURES + NORTTI_FIXTURES + NAMED_NORTTI_FIXTURES + FOLDED_FIXTURES
                     if os.path.exists(os.path.join(REPORTS, n + ".json"))]
    failed = 0
    for name in names:
        try:
            if name in NORTTI_FIXTURES:
                check_nortti(name)
            elif name in NAMED_NORTTI_FIXTURES:
                check_nortti_named(name)
            elif name in FOLDED_FIXTURES:
                check_folded(name)
            else:
                check_rtti(name)
            check_namespaces(name, load(name))
            check_puppy(name, load(name))
            check_struct_returns(name, load(name))
            check_construction(name, load(name))
            check_virtual_base(name, load(name))
            check_trunk(name, load(name))
            check_nonvirtual(name, load(name))
            check_complete_dtors(name, load(name))
            check_kennel(name, load(name))
            print("ok  ", name)
        except AssertionError as e:
            failed += 1
            print("FAIL", name, e)
        except FileNotFoundError:
            failed += 1
            print("MISSING", name)
    return 1 if failed else 0


if __name__ == "__main__":
    sys.exit(main(sys.argv[1:]))
