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
    # Without symbols: fetch and kind are the last two slots of the longest
    # table; play and rest both reach fetch, play reaches kind.
    longest = max((t for c in rep["classes"] for t in c["vtables"].values()), key=lambda t: len(t["slots"]))
    fetch = [v for v in rep["vcalls"] if v["targets"] == [longest["slots"][-1]]]
    kind = [v for v in rep["vcalls"] if v["targets"] == [longest["slots"][-2]]]
    assert len(fetch) >= 2 and len(kind) >= 1, (name, "Puppy::play and rest sites to the last slots", fetch, kind)


INLINED_CTORS = ("testprog_o2", "testprog_msvc64_nortti.exe")


def check_nortti(name):
    rep = load(name)
    check_coexistence(name, rep)
    classes = rep["classes"]
    inlined = name in INLINED_CTORS
    # Header-less tables (MSVC without RTTI) sit back to back; the split at
    # referenced slots must keep them apart: Puppy's table is the longest at 10.
    assert max(len(t["slots"]) for c in classes for t in c["vtables"].values()) <= 10, \
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
