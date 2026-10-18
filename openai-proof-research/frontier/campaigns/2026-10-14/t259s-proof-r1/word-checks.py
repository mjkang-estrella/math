#!/usr/bin/env python3
"""Reviewer-owned finite free-group identity checks for T259S. MIT.

Finite word identities only. They do not prove cost, measurability,
coverage, spectral gap or any infinite statement.
"""
import json

# Free group letters: positive ints are generators, negatives inverses.
A_ = 1                     # a
B = {i: 1 + i for i in range(1, 100)}   # b_i -> 2..100
C, D = 201, 202            # c, d in F(c,d)


def red(w):
    out = []
    for x in w:
        if out and out[-1] == -x:
            out.pop()
        else:
            out.append(x)
    return tuple(out)


def inv(w):
    return tuple(-x for x in reversed(w))


def mul(*ws):
    return red([x for w in ws for x in w])


def img(w, m):
    return mul(*[m[x] if x > 0 else inv(m[-x]) for x in w])


u = [()]
for i in range(1, 100):
    u.append(mul(u[-1], (A_,), (B[i],)))
w = mul(u[99], (A_,))
expect_w = tuple(x for i in range(1, 100) for x in (A_, B[i])) + (A_,)
assert w == expect_w

q = {A_: (D,)}
q[B[1]] = (-D, C)
q[B[2]] = (-D, -C)
for i in range(3, 100):
    q[B[i]] = (-D,)
assert img(u[0], q) == ()
assert img(u[1], q) == (C,)
for i in range(2, 100):
    assert img(u[i], q) == (), i
assert img(w, q) == (D,)
# Inverse substitution b_i = a^-1 u_{i-1}^-1 u_i recovers each b_i.
for i in range(1, 100):
    assert mul(inv((A_,)), inv(u[i - 1]), u[i]) == (B[i],)
# Row a-sources: prefixes u_i, i=0..99, are exactly the positions of a in w.
pos = [k for k, x in enumerate(w) if x == A_]
assert [w[:k] for k in pos] == [u[i] for i in range(100)]
exceptional = [i for i in range(100) if img(u[i], q) != ()]
assert exceptional == [1]
# H=<w,b1>: q(w)=d, q(b1)=d^-1 c; inverse substitution d->w, c->w b1.
psi = {D: w, C: mul(w, (B[1],))}
assert img(img((C,), psi), q) == (C,) and img(img((D,), psi), q) == (D,)
# Recovery word: u1^-1 . a b1 . (w) . reverse suffix ending at u1 a equals a.
suffix = w[len(mul(u[1], (A_,))):]           # b2 a b3 ... a b99 a
recovered = mul(inv((B[1],)), inv((A_,)), w, inv(suffix))
assert recovered == mul(inv(u[1]), u[1], (A_,)) == (A_,)
# Negative control: a second exceptional source breaks the row claim.
q2 = dict(q)
q2[B[2]] = (-D,)
q2[B[3]] = (-D, C)  # makes q(u2)=c? check it does not satisfy the frozen pattern
assert [i for i in range(100) if img(u[i], q2) != ()] != [1]
print(json.dumps({'status': 'PASS', 'row_sources': len(pos), 'exceptional_sources': exceptional,
                  'limits': 'finite word identities only; no measure, cost, spectral or novelty proof'},
                 sort_keys=True, indent=2))
