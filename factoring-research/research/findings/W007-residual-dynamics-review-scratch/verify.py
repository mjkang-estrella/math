"""Exact checks for the W007 residual-dynamics review.

Odd prime fields only. No factoring candidates, no height search.
Confirms the residual drift against the value pushforward, the depth-1
closed forms, the depth-3 generic root-count formula, and two explicit
reachable states.
"""

from fractions import Fraction


def legendre(a, p):
    a %= p
    if a == 0:
        return 0
    return 1 if pow(a, (p - 1) // 2, p) == 1 else -1


def primes_below(n):
    sieve = [True] * n
    sieve[0] = sieve[1] = False
    for i in range(2, int(n**0.5) + 1):
        if sieve[i]:
            for j in range(i * i, n, i):
                sieve[j] = False
    return [i for i in range(n) if sieve[i] and i > 2]


def moments(n, p):
    z = n[0]
    nonzero_square = 0
    cube = 0
    opposite = 0
    half = 0
    for y, value in enumerate(n):
        if y == 0:
            continue
        nonzero_square += value * value
        cube += value * value * value
        opposite += value * n[(-y) % p]
        half += n[(2 * y) % p] * value * value
    triple = 0
    for y, ny in enumerate(n):
        if y == 0 or ny == 0:
            continue
        for w, nw in enumerate(n):
            if w == 0 or nw == 0:
                continue
            s = (y + w) % p
            if s == 0:
                continue
            triple += ny * nw * n[s]
    return z, nonzero_square, cube, opposite, half, triple


def push_expectation(n, p):
    z, n2, n3, r, d, q = moments(n, p)
    predicted = Fraction(z * r + q - d - n3, p**3)
    total_v = Fraction(0)
    total_c = Fraction(0)
    weight = 0
    for a, wa in enumerate(n):
        if wa == 0:
            continue
        image = [0] * p
        for y, wy in enumerate(n):
            if wy:
                image[(y * ((y - a) % p)) % p] += wy
        if sum(image) != p:
            raise AssertionError("pushforward lost mass")
        collision = sum(v * v for v in image)
        residual = collision - image[0] * image[0]
        total_v += wa * residual
        total_c += wa * collision
        weight += wa
    if weight != p:
        raise AssertionError("weights do not sum to p")
    expected_v = Fraction(total_v, p * p * p)
    current_v = Fraction(n2, p * p)
    return predicted, expected_v - current_v, Fraction(total_c, p * p * p)


def main():
    failures = []
    for p in primes_below(60):
        laws = [[1] * p]
        laws.append([1 + legendre(y, p) for y in range(p)])
        for b in range(p):
            laws.append([1 + legendre((y - b) % p, p) for y in range(p)])
        atom = [0] * p
        atom[0] = p - 2
        atom[1] = 2
        laws.append(atom)
        for n in laws:
            predicted, actual, _ = push_expectation(n, p)
            if predicted != actual:
                failures.append((p, predicted, actual))
                break
    print("pushforward_mismatches", len(failures))

    second_mismatches = 0
    square_mismatches = 0
    for p in primes_below(80):
        eps = legendre(-1, p) + 2 * legendre(2, p)
        b = next(c for c in range(1, p) if legendre((-c) % p, p) == 1)
        n = [1 + legendre((y - b) % p, p) for y in range(p)]
        predicted, actual, _ = push_expectation(n, p)
        want = Fraction(p * p - 13 * p + 32 + eps, p**3)
        if actual != want:
            second_mismatches += 1
        squares = [1 + legendre(y, p) for y in range(p)]
        _, square_drift, _ = push_expectation(squares, p)
        chi2 = legendre(2, p)
        square_want = Fraction((p - 1) * (p - 11 if chi2 == 1 else p - 7), p**3)
        if square_drift != square_want:
            square_mismatches += 1
    print("generic_second_step_mismatches", second_mismatches)
    print("square_branch_mismatches", square_mismatches)

    # Fully expanded p=5 certificate: P(X)=X(X-1).
    p = 5
    n = [0] * p
    for x in range(p):
        n[(x * ((x - 1) % p)) % p] += 1
    print("p5_counts", n)
    weighted_residual = 0
    weighted_collision = 0
    for a, wa in enumerate(n):
        image = [0] * p
        for y, wy in enumerate(n):
            image[(y * ((y - a) % p)) % p] += wy
        collision = sum(v * v for v in image)
        residual = collision - image[0] * image[0]
        weighted_residual += wa * residual
        weighted_collision += wa * collision
        print(f"p5_a={a} weight={wa} image={image} collision={collision} residual={residual}")
    print("p5_E_residual_count", Fraction(weighted_residual, p), "over_p2", Fraction(weighted_residual, p**3))
    print("p5_E_collision_count", Fraction(weighted_collision, p))

    # Explicit near-cap branch.
    p = 17
    coeffs = (1, 8, 2, 15)
    hits = []
    for x in range(p):
        y = x
        for a in coeffs:
            y = y * ((y - a) % p) % p
        if y == 0:
            hits.append(x)
    print("F17_tuple", coeffs, "roots", len(hits), "missing", [x for x in range(p) if x not in hits])

    # Depth-3 generic root count, a0 nonzero, later training unrestricted.
    depth3_bad = 0
    for p in primes_below(40):
        # Enumerate r0 != 0, then r1, r2. a0 = r0 because P0 is the identity.
        total_roots = 0
        tuples = 0
        for a0 in range(1, p):
            for r1 in range(p):
                a1 = r1 * ((r1 - a0) % p) % p
                for r2 in range(p):
                    y = r2 * ((r2 - a0) % p) % p
                    a2 = y * ((y - a1) % p) % p
                    roots = 0
                    for x in range(p):
                        z = x * ((x - a0) % p) % p
                        z = z * ((z - a1) % p) % p
                        z = z * ((z - a2) % p) % p
                        if z == 0:
                            roots += 1
                    total_roots += roots
                    tuples += 1
        got = Fraction(total_roots, tuples)
        eps = legendre(-1, p) + 2 * legendre(2, p)
        want = Fraction(7 * p * p - 23 * p + 32 + eps, p * p)
        if got != want:
            depth3_bad += 1
            print("depth3_mismatch", p, got, want)
    print("depth3_mismatches", depth3_bad)

    # Depth-4 generic expectations cited in the review. a0 = r0 ≠ 0.
    cited = {17: Fraction(38731, 4913), 31: Fraction(271369, 29791)}
    for p, want in cited.items():
        total_roots = 0
        tuples = 0
        for a0 in range(1, p):
            for r1 in range(p):
                a1 = r1 * ((r1 - a0) % p) % p
                for r2 in range(p):
                    y1 = r2 * ((r2 - a0) % p) % p
                    a2 = y1 * ((y1 - a1) % p) % p
                    for r3 in range(p):
                        y = r3 * ((r3 - a0) % p) % p
                        y = y * ((y - a1) % p) % p
                        a3 = y * ((y - a2) % p) % p
                        roots = 0
                        for x in range(p):
                            z = x * ((x - a0) % p) % p
                            z = z * ((z - a1) % p) % p
                            z = z * ((z - a2) % p) % p
                            z = z * ((z - a3) % p) % p
                            if z == 0:
                                roots += 1
                        total_roots += roots
                        tuples += 1
        got = Fraction(total_roots, tuples)
        print(f"depth4_p{p}", got, "match", got == want)


if __name__ == "__main__":
    main()
