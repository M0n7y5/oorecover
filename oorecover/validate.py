"""Consistency checks on the class model, after OOAnalyzer's insanity rules.

Every finding names a contradiction between two conclusions; the conclusion
that rests on the weaker evidence is withdrawn, so a contradiction never
reaches the applied types. Findings are logged and reported.
"""


def _derives_from(cls, other, by_name, depth=0):
    if depth > 32:
        return False
    for b in cls.bases:
        if b.name == other.name:
            return True
        bc = by_name.get(b.name)
        if bc is not None and bc is not cls and _derives_from(bc, other, by_name, depth + 1):
            return True
    return False


def check_roles(classes, log=print, named_class=None):
    """Constructor and destructor attributions that cannot all be true.
    Runs before methods and members are attributed from those roles.
    named_class(fn) is the class a function's own symbol names, or None."""
    findings = []
    in_table = {}
    for c in classes:
        for t in c.vtables.values():
            for fn in t.functions:
                in_table.setdefault(fn, c)
    for c in classes:
        # A constructor is never virtual, so a constructor in a vtable is a
        # misread install order; the slot is the stronger evidence.
        for fn in sorted(c.ctors & set(in_table)):
            findings.append(("constructor in a vtable", c.name,
                             "%#x is a slot of %s" % (fn, in_table[fn].name)))
            c.ctors.discard(fn)
        for fn in sorted(c.ctors & c.dtors):
            findings.append(("constructor and destructor", c.name, "%#x" % fn))
            c.ctors.discard(fn)
            c.dtors.discard(fn)
    ctor_of = {fn: c for c in classes for fn in c.ctors}
    for c in classes:
        for fn in sorted(c.dtors):
            other = ctor_of.get(fn)
            if other is not None:
                # Destructor attribution reads install order backwards and is
                # the guess; the constructor claim stays.
                findings.append(("destructor is another class's constructor", c.name,
                                 "%#x constructs %s" % (fn, other.name)))
                c.dtors.discard(fn)
    # One function that constructs or destroys classes not related by
    # inheritance is one implementation the linker folded (empty
    # destructors). It is nobody's; the vtables decide whether a common base
    # can still type it.
    by_name = {c.name: c for c in classes}
    roles = {}
    for c in classes:
        for fn in c.ctors | c.dtors:
            roles.setdefault(fn, []).append(c)
    for fn, owners in sorted(roles.items()):
        if len(owners) < 2:
            continue
        tops = [c for c in owners
                if not any(o is not c and _derives_from(c, o, by_name) for o in owners)]
        if len(tops) >= 2 and all(c.has_rtti or c.bases for c in tops):
            findings.append(("folded into unrelated classes",
                             ", ".join(sorted(c.name for c in tops)), "%#x" % fn))
            for c in owners:
                c.ctors.discard(fn)
                c.dtors.discard(fn)
    if named_class is not None:
        # A constructor named for another class was attributed to a base
        # whose table it installs on the way (the derived table is missing
        # or its store unrecognised). The symbol decides: the function moves
        # to its own class when we model it, and is nobody's otherwise.
        by_name = {c.name: c for c in classes}
        for c in classes:
            for fn in sorted(c.ctors | c.dtors):
                name = named_class(fn)
                if name is None or name == c.name:
                    continue
                other = by_name.get(name)
                role = "ctors" if fn in c.ctors else "dtors"
                findings.append(("symbol names another class", c.name,
                                 "%#x belongs to %s%s" % (fn, name, "" if other else " (not modelled)")))
                getattr(c, role).discard(fn)
                if other is not None:
                    getattr(other, role).add(fn)
    for f in findings:
        log("[oorecover] contradiction: %s: %s (%s)" % f)
    return findings


def check_structure(classes, alloc_sizes, extent=None, log=print):
    """Layout conclusions that cannot all be true: base cycles, members past
    the allocated size, overlapping bases, an inferred base whose table is
    larger than the derived table it should be a prefix of. classes come
    bases first; extent(cls) recomputes a size once members were withdrawn."""
    findings = []
    by_name = {c.name: c for c in classes}
    for c in classes:
        for b in list(c.bases):
            bc = by_name.get(b.name)
            if bc is c or (bc is not None and _derives_from(bc, c, by_name)):
                findings.append(("inheritance cycle", c.name, "base %s" % b.name))
                c.bases.remove(b)
    # Two upper bounds on where a class's own members may end: the size its
    # allocations request (sizeof), and the offset at which the next base
    # starts in any class deriving from it. A member past either was read by
    # a method of some derived class that this class was credited with.
    bounds = {name: (size, "allocated %d" % size) for name, size in alloc_sizes.items()}
    for c in classes:
        laid = [(b.offset, b.name) for b in c.bases if b.offset is not None]
        offsets = sorted({off for off, _name in laid})
        for off, name in laid:
            # Empty bases share an offset with a real one; the bound is the
            # next base that actually starts further in.
            later = [o for o in offsets if o > off]
            if not later:
                continue
            room = later[0] - off
            if name not in bounds or room < bounds[name][0]:
                bounds[name] = (room, "%s lays a base at %d" % (c.name, later[0]))
    for c in classes:
        bound = bounds.get(c.name)
        if bound is None:
            continue
        limit, why = bound
        for off in sorted(c.members):
            size = c.members[off][0]
            if off + size > limit:
                findings.append(("member past the end of the object", c.name,
                                 "member at %d size %d, %s" % (off, size, why)))
                del c.members[off]
    if extent is not None:
        for c in classes:
            c.size = extent(c)
    for c in classes:
        ranges = []
        for b in c.bases:
            bc = by_name.get(b.name)
            if b.offset is None or bc is None or bc.size <= 0:
                continue
            for name, start, end in ranges:
                if b.offset < end and start < b.offset + bc.size:
                    findings.append(("overlapping bases", c.name,
                                     "%s at %d and %s at %d" % (name, start, b.name, b.offset)))
                    break
            else:
                ranges.append((b.name, b.offset, b.offset + bc.size))
    for c in classes:
        for b in list(c.bases):
            bc = by_name.get(b.name)
            if bc is None or b.offset is None:
                continue
            base_table = bc.vtables.get(0)
            derived_table = c.vtables.get(b.offset)
            if base_table is None or derived_table is None:
                continue
            if len(base_table.slots) > len(derived_table.slots):
                findings.append(("base table larger than the derived table", c.name,
                                 "%s has %d slots, table at %d has %d"
                                 % (b.name, len(base_table.slots), b.offset, len(derived_table.slots))))
                if not c.has_rtti:
                    # RTTI states the base; an inferred one is the guess.
                    c.bases.remove(b)
    for f in findings:
        log("[oorecover] contradiction: %s: %s (%s)" % f)
    return findings
