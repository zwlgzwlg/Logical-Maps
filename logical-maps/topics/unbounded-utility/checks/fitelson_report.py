#!/usr/bin/env python3
"""Diagnostics for the AI report communicated by Branden Fitelson.

Exact atom/block arithmetic and numerical checks of analytic witnesses.
The accompanying write-ups, not these samples, prove the infinite-law claims.
Run from logical-maps/: python3 topics/unbounded-utility/checks/fitelson_report.py
"""

from fractions import Fraction as F
import math


def clip(x, a, b):
    return max(-a, min(x, b))


def alternating(a, b, scale=1):
    """Exact clipped expectation, including both infinite geometric tails."""
    a, b = F(a), F(b)
    j = 0
    value = F(0)
    while scale * 2 ** (j + 1) <= max(a, b):
        j += 1
        value += F(1, 2**j) * clip(scale * (-2)**j, a, b)
    odd = j + 1 if (j + 1) % 2 else j + 2
    even = j + 1 if (j + 1) % 2 == 0 else j + 2
    return value - a * F(4, 3 * 2**odd) + b * F(4, 3 * 2**even)


def symmetric_geometric(base, a, b):
    """Mass (base-1)/(2 base**j) at each of +/-base**j, j>=1."""
    a, b = F(a), F(b)
    j = 0
    value = F(0)
    while base ** (j + 1) <= max(a, b):
        j += 1
        r = base**j
        value += F(base - 1, 2 * r) * (clip(r, a, b) + clip(-r, a, b))
    return value + (b - a) * F(1, 2 * base**j)


def cauchy_positive_clip(r):
    return (r * math.atan(1 / r) + 0.5 * math.log1p(r * r)) / math.pi


def levy_clip(t):
    x = 1 / (2 * math.sqrt(t))
    return (t * math.erf(x) + math.sqrt(t / math.pi) * math.exp(-x*x)
            - 0.5 * math.erfc(x))


def noise_cdf(x):
    return 0.5 / math.sqrt(1-x) if x < 0 else 1 - 0.5 / math.sqrt(1+x)


def block_convolution(x, w, length, h, height):
    p = (noise_cdf(x+length) - noise_cdf(x)
         + noise_cdf(x-w) - noise_cdf(x-w-length))
    n = noise_cdf(x) - noise_cdf(x-w)
    return height*p - h*n


def check_atom_witnesses():
    for n in range(1, 18):
        a, b = F(7, 4)*4**n, 2*4**n
        assert alternating(a, b) == F(-1, 2)
        assert alternating(a, b, 2) == F(-1, 2)
        assert alternating(4**n, 4**n) == F(-1, 3)
        assert alternating(2*4**n, 2*4**n) == F(-2, 3)
        assert symmetric_geometric(4, 4**n, 2*4**n) == F(1, 2)
        assert symmetric_geometric(4, 2*4**n, 4*4**n) == 1
    for t in [F(1), F(3, 2), F(2), F(7, 3), F(17), F(101, 7), F(4096)]:
        assert symmetric_geometric(2, t, 2*t) == F(1, 2)
        assert alternating(t, 2*t) == 0
    print('PASS: exact alternating-game and symmetric geometric witnesses')


def check_blocks():
    c = F(3, 13)
    atoms = {}
    segments = []
    start = 0
    previous = F(0)
    sum_heights = sum_depths = F(0)
    for k in range(1, 13):
        w, length = 4**k-1, 16**k-1
        h, height = c/F(4**k), 2*c/F(2**k)
        delta = F(1, 2**k)-F(1, 4**k)
        assert length >= 2*w and height*delta >= h
        assert h*w == c*(1-F(1, 4**k))
        assert 2*height*length-h*w > 0
        for left, width, value in [(start, length, height),
                                    (start+length, w, -h),
                                    (start+length+w, length, height)]:
            atoms[left] = atoms.get(left, F(0)) + previous-value
            previous = value
            segments.append((left, left+width, value))
        start += 2*length+w
        sum_heights += height
        sum_depths += h
        if k <= 5:
            points = [-100*length, -3*length, -length, -w, 0, w/2, w,
                      2*w, length, w+length, 3*length, 100*length]
            points += [j*length/20 for j in range(-60, 61)]
            for x in points:
                y = block_convolution(x, w, length, float(h), float(height))
                assert y >= -1e-12*float(height+h), (k, x, y)
    atoms[start] = previous  # return the finite prefix to zero
    assert sum(atoms.values()) == 0
    variation = sum(abs(m) for m in atoms.values())
    assert variation == 2*c + 2*(sum_heights+sum_depths)
    assert F(20, 13)-variation == 4*c/F(2**12) + 2*c/F(3*4**12)
    positive = sum(m for m in atoms.values() if m > 0)
    negative = -sum(m for m in atoms.values() if m < 0)
    assert positive == negative == variation/2 < 1
    for left, right, value in segments:
        midpoint = F(left+right, 2)
        assert sum(m for x, m in atoms.items() if x > midpoint) == value
    print('PASS: block inequalities, Jordan masses, survival reconstruction and convolution samples')


def check_limits():
    kappa = math.log(8/7)/math.pi
    for n in [5, 10, 15]:
        a, b = 7*4**n/4, 2*4**n
        gap = cauchy_positive_clip(b)-cauchy_positive_clip(a)
        assert abs(gap-kappa) < 1/a
    for t in [1e4, 1e6, 1e8]:
        gap = 2*levy_clip(t/4)-levy_clip(t)
        assert gap < 0 and abs(gap+0.5) < 1/math.sqrt(t)
        comonotonic = 2*(cauchy_positive_clip(t)-cauchy_positive_clip(t/2))
        assert abs(comonotonic-2*math.log(2)/math.pi) < 2/t
    print('PASS: Cauchy and Levy limiting gaps')


def check_shuffle():
    count = 4096
    shifted = []
    pairs = []
    for j in range(count):
        other = j + count//4 if (j//(count//4)) % 2 == 0 else j-count//4
        shifted.append(other)
        u, v = (j+0.5)/count, (other+0.5)/count
        x = math.tan(math.pi*(u-0.5))**3
        z0 = math.tan(math.pi*(v-0.5))
        z = math.copysign(z0*z0, z0)
        assert min(abs(x), abs(z)) <= 1+1e-12
        pairs.append((x, z))
    assert sorted(shifted) == list(range(count))
    for a, b in [(2, 2), (10, 20), (100, 10000), (1000000, 2000000)]:
        errors = []
        for x, z in pairs:
            error = abs(clip(x+z, a, b)-clip(x, a, b)-clip(z, a, b))
            assert error <= 2*min(abs(x), abs(z))+1e-9
            errors.append(error)
        if a == 1000000:
            assert sum(errors)/count < 0.01
    print('PASS: one fixed shuffle, uniform marginals and bounded clipping defects')


if __name__ == '__main__':
    check_atom_witnesses()
    check_blocks()
    check_limits()
    check_shuffle()
