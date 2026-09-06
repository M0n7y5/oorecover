import os
import sys

sys.path.insert(0, os.path.dirname(os.path.dirname(os.path.abspath(__file__))))

from oorecover.itanium import demangle_typeinfo_name  # noqa: E402
from oorecover.msvc import demangle_typename  # noqa: E402


def test_itanium_simple():
    assert demangle_typeinfo_name("3Dog") == "Dog"
    assert demangle_typeinfo_name("6Animal") == "Animal"


def test_itanium_namespaced():
    assert demangle_typeinfo_name("N3zoo3DogE") == "zoo::Dog"
    assert demangle_typeinfo_name("N1a1b1cE") == "a::b::c"


def test_itanium_std():
    assert demangle_typeinfo_name("St9exception") == "std::exception"
    assert demangle_typeinfo_name("NSt3__112basic_stringE") == "std::__1::basic_string"


def test_itanium_template_kept_raw():
    assert demangle_typeinfo_name("N3abc6VectorIiEE") == "abc::Vector<i>"


def test_itanium_local_prefix():
    assert demangle_typeinfo_name("*N12_GLOBAL__N_13FooE") == "_GLOBAL__N_1::Foo"


def test_itanium_garbage_rejected():
    assert demangle_typeinfo_name("") is None
    assert demangle_typeinfo_name("hello world") is None
    assert demangle_typeinfo_name("9Short") is None
    assert demangle_typeinfo_name("N3abcE trailing") is None


def test_msvc_simple():
    assert demangle_typename(".?AVDog@zoo@@") == "zoo::Dog"
    assert demangle_typename(".?AUPoint@@") == "Point"
    assert demangle_typename(".?AW4Color@gfx@@") == "gfx::Color"
    assert demangle_typename(".?AVInner@Outer@ns@@") == "ns::Outer::Inner"


def test_msvc_templates():
    assert demangle_typename(".?AV?$vector@HV?$allocator@H@std@@@std@@") == \
        "std::vector<int, std::allocator<int>>"
    assert demangle_typename(".?AV?$ControlElement@VControlLabel@QMdi@@@QMdi@@") == \
        "QMdi::ControlElement<QMdi::ControlLabel>"
    assert demangle_typename(".?AU?$pair@H_N@std@@") == "std::pair<int, bool>"
    assert demangle_typename(".?AVCloseButton@?A0x024c7af8@@") == "(anonymous namespace)::CloseButton"


def test_msvc_rejected():
    assert demangle_typename("") is None
    assert demangle_typename("Dog@zoo@@") is None
    assert demangle_typename(".?AVDog@zoo@") is None
    assert demangle_typename(".?AV?$vector@H@std@") is None


if __name__ == "__main__":
    for name in sorted(n for n in dir() if n.startswith("test_")):
        globals()[name]()
        print("ok", name)
