#!/usr/bin/env python3
"""Exact supporting arithmetic for the St Petersburg incompleteness proof.

Infinite St Petersburg laws are reduced symbolically, never truncated.
The written proof supplies the quantified mathematical argument.
"""

from collections import defaultdict
from fractions import Fraction as F


def shifted_law(s, x_side, background):
    law = defaultdict(F)
    law["atom", 0] += F(s - 1, 5)
    root = 2 * s + (1 if x_side else 2)
    head_shifts = [2 * s] if background == 0 else [2 * s + 1, 2 * s + 2]
    for z in head_shifts:
        law["atom", root + z] += F(1, 5 * len(head_shifts))
    for positive in (True, False):
        mass = F(2, 5) if positive else F(2, 5 * s)
        base = s + 2 if x_side else (s + 1 if positive else 2 * s + 2)
        if background == 0:
            shifts = [s]
        elif background == 1:
            shifts = [s + 1, 2 * s] if positive else [2 * s]
        else:
            shifts = [2 * s + 1, 3 * s] if positive else [3 * s, 2 * s + 2]
        for z in shifts:
            law["S", base + z] += mass / len(shifts)
    assert sum(law.values()) == 1
    assert all(c >= 0 for c in law.values())
    return law


def canonical_signed_law(law):
    """Use law(2aS)=2 law(aS)-delta_(2a) until a is odd."""
    result = defaultdict(F)
    for (kind, multiplier), coefficient in law.items():
        if kind == "S":
            while multiplier % 2 == 0:
                result["atom", multiplier] -= coefficient
                coefficient *= 2
                multiplier //= 2
        result[kind, multiplier] += coefficient
    return {key: value for key, value in result.items() if value}


def check_infinite_law_identity():
    for s in (1, 2):
        difference = defaultdict(F)
        for j in range(3):
            for side, sign in ((True, 1), (False, -1)):
                for key, coefficient in shifted_law(s, side, j).items():
                    difference[key] += sign * coefficient
        assert canonical_signed_law(difference) == {
            ("atom", 4 * s + 1): F(1, 5),
            ("atom", 4 * s + 2): F(-1, 5),
        }


def check_monotonicity():
    for s in (1, 2):
        assert F(s - 1, 5) + F(1, 5) + F(2, 5) + F(2, 5 * s) == 1
        # Quantile ordering, including head -> P1 and N_k -> P_(k+1).
        assert 2 * s + 1 <= 2 * (s + 2)
        assert s + 1 <= s + 2 <= 2 * (s + 1)
        for head, positive, negative in (
            ([2 * s], [s], [s]),
            ([2 * s + 1, 2 * s + 2], [s + 1, 2 * s], [2 * s]),
            ([2 * s + 1, 2 * s + 2], [2 * s + 1, 3 * s], [3 * s, 2 * s + 2]),
        ):
            assert head == sorted(head)
            assert positive == sorted(positive)
            assert negative == sorted(negative)
            assert head[-1] <= 2 * positive[0]
            assert positive[-1] <= negative[0]
            assert negative[-1] <= 2 * positive[0]


def check_equal_mean_connection():
    assert F(4, 5) * 2 == F(2, 5) * 1 + F(3, 5) * 2
    # The head differences sum to (-1,+1); the shared remainder increases.
    assert (-1 + 0, 2 - 1) == (-1, 1)
    assert [3 + 0 - 0, 6 + 5 - 2, 6 + 8 - 2, 12 + 8 - 2] == [3, 9, 12, 18]
    blocks = {}
    for s in (1, 2):
        position = F(0)
        pieces = []
        values = [(F(s - 1, 5), 0), (F(1, 5), -1)]
        for k in range(1, 13):
            t = 2**k
            values.extend(((F(2, 5 * t), t), (F(2, 5 * s * t), -s * t)))
        for length, width in values:
            if length:
                pieces.append((position, position + length, width))
            position += length
        blocks[s] = pieces
    # Check the two independently constructed quantile partitions on their
    # common finite prefix. The write-up proves the matching tail pattern.
    end = min(blocks[s][-1][1] for s in blocks)
    endpoints = sorted({v for pieces in blocks.values() for a, b, _ in pieces
                        for v in (a, b) if v <= end} | {end})
    for a, b in zip(endpoints, endpoints[1:]):
        u = (a + b) / 2
        widths = [next(w for lo, hi, w in blocks[s] if lo <= u < hi) for s in (1, 2)]
        expected = -1 if u < F(1, 5) else 1 if u < F(2, 5) else 0
        assert sum(widths) == expected


if __name__ == "__main__":
    check_infinite_law_identity()
    check_monotonicity()
    check_equal_mean_connection()
    print("PASS: exact infinite-law identities, increasing backgrounds, equal-mean connection")
