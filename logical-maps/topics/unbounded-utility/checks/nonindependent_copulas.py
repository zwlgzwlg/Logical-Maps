#!/usr/bin/env python3
"""Exact finite diagnostics for the nonindependent-copula write-up.

The universal claims are proved in the write-up; these calculations check
the concrete density, binary mixture obstruction, and signed mean identity.
"""

from collections import defaultdict
from fractions import Fraction as F


def main():
    f = (0, 1, -1, 0)
    c = [[F(1, 16) * (1 + F(1, 2) * x * y) for y in f] for x in f]
    assert all(v > 0 for row in c for v in row)
    assert all(sum(row) == F(1, 4) for row in c)
    assert all(sum(c[i][j] for i in range(4)) == F(1, 4) for j in range(4))
    assert sum(c[i][j] for i in range(2) for j in range(2)) == F(9, 32)

    # Binary mixture test: the sum's zero mass differs from product mixing.
    x = (0, 0, 2, 2)
    z = (0, 0, 1, 1)
    actual, mixed = defaultdict(F), defaultdict(F)
    for i in range(4):
        for j in range(4):
            actual[x[i] + z[j]] += c[i][j]
            mixed[x[i] + z[j]] += F(1, 16)
    assert actual[0] == F(9, 32) != mixed[0] == F(1, 4)
    assert sum(k * v for k, v in actual.items()) == sum(k * v for k, v in mixed.items())

    # An interior perturbation does not involve extreme quantiles.
    qx, qz = (-10**12, -2, 5, 10**15), (-10**14, 1, 3, 10**13)
    difference = defaultdict(F)
    for i in range(4):
        for j in range(4):
            difference[qx[i] + qz[j]] += c[i][j] - F(1, 16)
    difference = {k: v for k, v in difference.items() if v}
    assert set(difference) <= {-1, 1, 6, 8}
    assert sum(difference.values()) == 0
    assert sum(k * v for k, v in difference.items()) == 0
    # For the adjacent-quarter shuffle the (1/4,1/4) rectangle has mass 0.
    permutation = (1, 0, 3, 2)
    assert permutation[0] != 0
    print("PASS: copula marginals, binary noncommutation, bounded zero-mean perturbation")


if __name__ == "__main__":
    main()
