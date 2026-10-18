#!/usr/bin/env python3
"""Finite free-group word checks for the routine-lift comparison in review.md.

MIT. Reviewer-owned. Reads nothing, writes nothing. These are exact word identities
and index bookkeeping only; they prove no measure, cost, spectral or novelty claim.

Encoding: in A, a=1 and b_i=i+1 (1<=i<=99); in F(c,d), c=1 and d=2; negatives are inverses.
"""
import json


def red(w):
    out = []
    for x in w:
        if out and out[-1] == -x:
            out.pop()
        else:
            out.append(x)
    return tuple(out)


def mul(*ws):
    return red(x for w in ws for x in w)


def inv(w):
    return tuple(-x for x in reversed(w))


def image(w, m):
    return mul(*(m[x] if x > 0 else inv(m[-x]) for x in w))


def power(g, n):
    return mul(*([g] * n)) if n >= 0 else inv(power(g, -n))


def main():
    a = (1,)
    u = [()]
    for i in range(1, 100):
        u.append(mul(u[-1], a, (i + 1,)))
    w = mul(u[-1], a)
    c, d = (1,), (2,)

    # Candidate quotient q: q(a)=d, q(u_1)=c, q(u_i)=1 (i>=2).
    q = {1: d, 2: mul(inv(d), c), 3: mul(inv(d), inv(c)), **{i: inv(d) for i in range(4, 101)}}
    assert [image(v, q) for v in u] == [(), c] + [()] * 98
    assert image(w, q) == d

    # Comparison lift q2 of the source height chi: q2(a)=d, q2(u_i)=c^i, so q2(b_i)=d^-1 c.
    q2 = {1: d, **{i: mul(inv(d), c) for i in range(2, 101)}}
    assert [image(v, q2) for v in u] == [power(c, i) for i in range(100)]
    w2 = image(w, q2)
    assert w2 == mul(power(c, 99), d)

    # chi = pi o q2 with pi(c)=pi(d)=1: exponent sums reproduce chi(u_i)=i, chi(w)=100.
    def expsum(word):
        return sum(1 if x > 0 else -1 for x in word)
    assert [expsum(image(v, q2)) for v in u] == list(range(100))
    assert expsum(w2) == 100

    # Source sliding-window bookkeeping with q2: for v with coordinate in E c^(k+99),
    # y=v u_99^-1 and the a-sources y u_(i-1), i=1..99, have coordinates in E c^(k+i-1),
    # i.e. exactly the 99 preceding translates; y w = v a.
    shifts = [expsum(mul(inv(image(u[99], q2)), image(u[i - 1], q2))) for i in range(1, 100)]
    assert shifts == [i - 1 - 99 for i in range(1, 100)]
    assert mul(inv(u[99]), w) == a

    # H=<w,b1> under q2: images c^99 d and d^-1 c do not commute, hence generate a free
    # subgroup of rank two, and q2|H is injective (rank-two free groups are Hopfian).
    x, y = w2, image((2,), q2)
    assert mul(x, y) != mul(y, x)

    # Candidate's H-images d and d^-1 c: inverse substitution recovers both generators.
    psi = {1: mul(w, (2,)), 2: w}
    assert image(image(w, q), psi) == w and image(image((2,), q), psi) == (2,)

    print(json.dumps({
        "status": "PASS",
        "candidate_q_images_checked": 100,
        "lift_q2_images_checked": 100,
        "lift_q2_window_offsets": sorted(set(shifts))[:1] + sorted(set(shifts))[-1:],
        "lift_q2_H_noncommuting": True,
        "limits": "finite word identities only; no Borel, cost, spectral, mixing or novelty proof",
    }, sort_keys=True, indent=2))


if __name__ == "__main__":
    main()
