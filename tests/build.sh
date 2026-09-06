#!/bin/sh
# Builds the fixture matrix. Missing toolchains skip their fixtures.
set -u
cd "$(dirname "$0")"
SRC=testprog.cpp
built=""

try() {
    name=$1; shift
    if "$@" 2>/dev/null; then built="$built $name"; else echo "skip $name"; rm -f "$name"; fi
}

try testprog          g++ -O1 -fno-inline -o testprog $SRC
try testprog_stripped g++ -O1 -fno-inline -s -o testprog_stripped $SRC
try testprog_nortti   g++ -O1 -fno-inline -fno-rtti -s -o testprog_nortti $SRC
try testprog_o2       g++ -O2 -fno-rtti -s -o testprog_o2 $SRC
try testprog_nortti_sym g++ -O1 -fno-inline -fno-rtti -o testprog_nortti_sym $SRC
try testprog32        g++ -m32 -O1 -fno-inline -s -o testprog32 $SRC
# Identical functions of unrelated classes folded into one by the linker.
try testprog_icf      g++ -O2 -fuse-ld=lld -Wl,--icf=all -o testprog_icf $SRC
# Function symbols without vtable symbols: linkers merge or hide vtables, and
# MSVC PDBs often carry only the methods. Class names then come from the
# constructor symbols.
strip_vtable_symbols() {
    cp testprog_nortti_sym "$1" || return 1
    args=$(nm "$1" | sed -n 's/.* \(_ZTVN.*\)$/--strip-symbol=\1/p')
    [ -n "$args" ] && objcopy $args "$1"
}
try testprog_nortti_novt strip_vtable_symbols testprog_nortti_novt

printf '\t.section .rdata,"dr"\n\t.globl "??_7type_info@@6B@"\n"??_7type_info@@6B@":\n\t.quad 0\n\t.quad 0\n' > msvc_rt64.s
printf '\t.section .rdata,"dr"\n\t.globl "??_7type_info@@6B@"\n"??_7type_info@@6B@":\n\t.long 0\n\t.long 0\n' > msvc_rt32.s
CL="clang-cl /nologo /O1 /GS- /GR /EHs-c- /Zl"
try testprog_msvc64.exe sh -c "clang -c --target=x86_64-pc-windows-msvc -o msvc_rt64.obj msvc_rt64.s && $CL /c /Fotestprog64.obj $SRC && lld-link /nologo /nodefaultlib /entry:main /subsystem:console /out:testprog_msvc64.exe testprog64.obj msvc_rt64.obj"
try testprog_msvc32.exe sh -c "clang -c --target=i386-pc-windows-msvc -o msvc_rt32.obj msvc_rt32.s && $CL -m32 /c /Fotestprog32.obj $SRC && lld-link /nologo /nodefaultlib /entry:main /subsystem:console /machine:x86 /safeseh:no /out:testprog_msvc32.exe testprog32.obj msvc_rt32.obj"
# No RTTI and no symbols: vftables sit back to back with nothing between them.
try testprog_msvc64_nortti.exe sh -c "clang -c --target=x86_64-pc-windows-msvc -o msvc_rt64.obj msvc_rt64.s && $CL /GR- /c /Fotestprog64n.obj $SRC && lld-link /nologo /nodefaultlib /entry:main /subsystem:console /out:testprog_msvc64_nortti.exe testprog64n.obj msvc_rt64.obj"
rm -f msvc_rt64.s msvc_rt32.s msvc_rt64.obj msvc_rt32.obj testprog64.obj testprog32.obj testprog64n.obj
echo "built:$built"
