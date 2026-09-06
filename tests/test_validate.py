import os
import sys
from types import SimpleNamespace

sys.path.insert(0, os.path.dirname(os.path.dirname(os.path.abspath(__file__))))

from oorecover.facts import BaseRef  # noqa: E402
from oorecover.validate import check_roles, check_structure  # noqa: E402


def table(*functions):
    return SimpleNamespace(functions=list(functions), slots=list(functions))


def cls(name, vtables=None, ctors=(), dtors=(), bases=(), members=None, size=0, rtti=False):
    return SimpleNamespace(name=name, vtables=vtables or {}, ctors=set(ctors), dtors=set(dtors),
                           bases=list(bases), members=dict(members or {}), size=size, has_rtti=rtti)


def quiet(_msg):
    pass


def extent(c):
    end = 0
    for off, m in c.members.items():
        end = max(end, off + m[0])
    return end


def test_constructor_in_vtable_withdrawn():
    a = cls("A", vtables={0: table(0x100, 0x200)}, ctors={0x300, 0x200})
    findings = check_roles([a], quiet)
    assert [f[0] for f in findings] == ["constructor in a vtable"]
    assert a.ctors == {0x300}


def test_constructor_and_destructor_withdrawn():
    a = cls("A", ctors={0x300}, dtors={0x300, 0x400})
    findings = check_roles([a], quiet)
    assert [f[0] for f in findings] == ["constructor and destructor"]
    assert a.ctors == set() and a.dtors == {0x400}


def test_destructor_that_constructs_another_class():
    a = cls("A", ctors={0x300})
    b = cls("B", dtors={0x300})
    findings = check_roles([a, b], quiet)
    assert [f[0] for f in findings] == ["destructor is another class's constructor"]
    assert a.ctors == {0x300} and b.dtors == set()


def test_constructor_named_for_another_class():
    base = cls("Base", ctors={0x100, 0x200})
    derived = cls("Derived")
    names = {0x100: "Base", 0x200: "Derived", 0x300: "Unknown"}
    base.dtors.add(0x300)
    findings = check_roles([base, derived], quiet, names.get)
    assert [f[0] for f in findings] == ["symbol names another class"] * 2, findings
    assert base.ctors == {0x100} and base.dtors == set() and derived.ctors == {0x200}


def test_consistent_roles_untouched():
    a = cls("A", vtables={0: table(0x100)}, ctors={0x300}, dtors={0x100})
    assert check_roles([a], quiet) == []
    assert a.ctors == {0x300} and a.dtors == {0x100}


def test_inheritance_cycle_broken():
    a = cls("A", bases=[BaseRef("B", 0, False)], size=8)
    b = cls("B", bases=[BaseRef("A", 0, False)], size=8)
    findings = check_structure([a, b], {}, log=quiet)
    assert [f[0] for f in findings] == ["inheritance cycle"]
    assert not a.bases and b.bases


def test_member_past_allocation_dropped():
    a = cls("A", members={8: [4, "int", 1, 0], 40: [8, "ptr", 0, 1]}, size=48)
    findings = check_structure([a], {"A": 24}, extent, log=quiet)
    assert [f[0] for f in findings] == ["member past the end of the object"]
    assert a.size == 12
    assert sorted(a.members) == [8]


def test_member_past_next_base_dropped():
    a = cls("A", members={8: [4, "int", 1, 0], 40: [8, "ptr", 0, 1]}, size=48)
    empty = cls("Tag", size=0)
    b = cls("B", size=16)
    d = cls("D", bases=[BaseRef("A", 0, False), BaseRef("Tag", 0, False), BaseRef("B", 32, False)], size=48)
    findings = check_structure([a, empty, b, d], {}, extent, log=quiet)
    assert [f[0] for f in findings] == ["member past the end of the object"], findings
    assert "D lays a base at 32" in findings[0][2]
    assert sorted(a.members) == [8]


def test_member_within_allocation_kept():
    a = cls("A", members={8: [4, "int", 1, 0], 16: [8, "ptr", 0, 1]}, size=24)
    assert check_structure([a], {"A": 24}, log=quiet) == []
    assert sorted(a.members) == [8, 16]


def test_overlapping_bases_reported():
    b = cls("B", size=24)
    c = cls("C", size=24)
    d = cls("D", bases=[BaseRef("B", 0, False), BaseRef("C", 16, False)], size=40)
    findings = check_structure([b, c, d], {}, log=quiet)
    assert [f[0] for f in findings] == ["overlapping bases"]


def test_inferred_base_with_larger_table_dropped():
    base = cls("B", vtables={0: table(1, 2, 3, 4)}, size=8)
    derived = cls("D", vtables={0: table(1, 2)}, bases=[BaseRef("B", 0, False)], size=8)
    findings = check_structure([base, derived], {}, log=quiet)
    assert [f[0] for f in findings] == ["base table larger than the derived table"]
    assert derived.bases == []


def test_rtti_base_with_larger_table_kept():
    base = cls("B", vtables={0: table(1, 2, 3, 4)}, size=8)
    derived = cls("D", vtables={0: table(1, 2)}, bases=[BaseRef("B", 0, False)], size=8, rtti=True)
    findings = check_structure([base, derived], {}, log=quiet)
    assert [f[0] for f in findings] == ["base table larger than the derived table"]
    assert len(derived.bases) == 1


if __name__ == "__main__":
    names = [n for n in dir() if n.startswith("test_")]
    for n in names:
        globals()[n]()
    print("ok  test_validate (%d)" % len(names))
