"""Check the alternation and recoloring lemmas on every labelled preorder of size at most four."""
from itertools import product


def preorders(size):
    for rows in product(range(1 << size), repeat=size):
        reflexive = all(row & (1 << i) for i, row in enumerate(rows))
        if reflexive and all(rows[j] & ~row == 0 for row in rows
                             for j in range(size) if row & (1 << j)):
            yield rows


def diamond(rows, region):
    return sum(1 << i for i, row in enumerate(rows) if row & region)


def layers(rows, positive):
    """The two entries give the regions admitting n alternations from the specified bit."""
    universe = (1 << len(rows)) - 1
    bits = universe ^ positive, positive
    current = bits
    levels = []
    for _ in range(len(rows) + 3):
        following = bits[0] & diamond(rows, current[1]), bits[1] & diamond(rows, current[0])
        exact = current[0] & ~following[0], current[1] & ~following[1]
        levels.append((current, following, exact))
        current = following
    return levels


def check():
    frames = tests = pointed_cases = 0
    for size in range(1, 5):
        for rows in preorders(size):
            frames += 1
            colorings = {p: layers(rows, p) for p in range(1 << size)}
            for p, levels in colorings.items():
                for n in range(size + 1):
                    current, following, exact = levels[n]
                    assert all((following[b] & ~current[b]) == 0 for b in (0, 1))
                    region = current[0] | current[1]
                    assert diamond(rows, region) == region
                    tests += 1
                    for bit in (0, 1):
                        cap = following[0] | following[1]
                        recolored = (p & ~cap) | (cap if bit == 0 else 0)
                        higher_exact = colorings[recolored][n + 1][2][1 - bit]
                        roots = cap & diamond(rows, exact[bit])
                        assert (roots & ~higher_exact) == 0
                        pointed_cases += roots.bit_count()
    assert frames == 389 and pointed_cases == 9620
    print(f"{frames} preorders, {tests} layer tests, {pointed_cases} pointed recolorings")


if __name__ == "__main__":
    check()
