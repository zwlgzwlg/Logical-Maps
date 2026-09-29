"""Finite checks of the Boolean-valued selector calculation.

Run from logical-maps/ with:
    python3 topics/classicism/checks/boolean_valued_choice.py

Powerset algebras are finite and atomic. These checks verify the formula
calculations in full-boolean-valued-atom-and-atomless.md, not the infinite
atomless countermodel or its full higher-order hierarchy.
"""

from itertools import product


def meet(values, top):
    result = top
    for value in values:
        result &= value
    return result


def join(values):
    result = 0
    for value in values:
        result |= value
    return result


def main():
    total_selectors = 0
    for size in range(1, 5):
        top = (1 << size) - 1
        elements = tuple(range(top + 1))
        atoms = {1 << index for index in range(size)}

        def relation(p, q):
            return (p if q == top else 0) | (top ^ p if q == 0 else 0)

        def implies(p, q):
            return (top ^ p) | q

        def equal(p, q):
            return top if p == q else 0

        serial = meet((join(relation(p, q) for q in elements)
                       for p in elements), top)
        functional = meet((join(
            relation(p, q) & meet(
                (implies(relation(p, r), equal(q, r)) for r in elements), top
            ) for q in elements
        ) for p in elements), top)
        assert serial == functional == top

        selector_meets = set()
        for outputs in product((0, top), repeat=len(elements)):
            value = meet((relation(p, q) for p, q in zip(elements, outputs)), top)
            selector_meets.add(value)
            total_selectors += 1
        # A selector using any other output has a zero factor, so this
        # enumeration includes every nonzero existential contribution.
        for p in elements:
            for q in elements:
                if q not in (0, top):
                    assert relation(p, q) == 0
        assert selector_meets == {0} | atoms
        assert join(selector_meets) == top

        for atom in atoms:
            outputs = [top if p & atom else 0 for p in elements]
            assert meet((relation(p, q) for p, q in zip(elements, outputs)), top) == atom

        # Exhaust all subsets, including the empty family, to check the
        # designated atom evaluation's finite quantifier semantics.
        for included in product((False, True), repeat=len(elements)):
            family = [p for p, present in zip(elements, included) if present]
            universal = meet(family, top)
            existential = join(family)
            for atom in atoms:
                assert bool(universal & atom) == all(bool(p & atom) for p in family)
                assert bool(existential & atom) == any(bool(p & atom) for p in family)

        print(f'{size} atoms: serial and functional value is top; '
              f'nonzero selector meets are exactly the {size} atoms.')
    print(f'PASS: {total_selectors} selectors and all finite quantifier families; '
          'the infinite atomless component is established in the write-up.')


if __name__ == '__main__':
    main()
