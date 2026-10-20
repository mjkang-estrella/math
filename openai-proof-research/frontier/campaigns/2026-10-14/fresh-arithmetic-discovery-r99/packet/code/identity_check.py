#!/usr/bin/env python3
"""Random-evaluation check of the update identities (Lemma 4) and of the
block-selection index conditions (Section 5, Step 5) in proof.md.

Fields used: F_q for a few primes q (including 2, 3) and GF(2^8).
Passing is evidence about the algebra only; it is not a proof.
"""
import itertools
import random
import sys

random.seed(20261020)


class Fp:
    def __init__(self, q):
        self.q = q

    def rand_nonzero(self):
        return random.randrange(1, self.q)

    def rand(self):
        return random.randrange(self.q)

    def add(self, a, b):
        return (a + b) % self.q

    def mul(self, a, b):
        return (a * b) % self.q

    def inv(self, a):
        return pow(a, self.q - 2, self.q)

    def pow(self, a, z):
        return pow(a, z, self.q) if z >= 0 else pow(self.inv(a), -z, self.q)


class GF256:
    """GF(2^8) with modulus x^8 + x^4 + x^3 + x + 1."""

    q = 256

    def rand_nonzero(self):
        return random.randrange(1, 256)

    def rand(self):
        return random.randrange(256)

    def add(self, a, b):
        return a ^ b

    def mul(self, a, b):
        r = 0
        while b:
            if b & 1:
                r ^= a
            a <<= 1
            if a & 0x100:
                a ^= 0x11B
            b >>= 1
        return r

    def pow(self, a, z):
        if z < 0:
            a, z = self.inv(a), -z
        r = 1
        for _ in range(z):
            r = self.mul(r, a)
        return r

    def inv(self, a):
        return self.pow(a, 254)


def subsets(n):
    for m in range(1 << n):
        yield frozenset(j + 1 for j in range(n) if m >> j & 1)


def gt(S, T):
    return not T or (S and min(S) > max(T))


def s(J):
    return sum(2 ** j for j in J)


def prod(K, x, J):
    r = 1
    for j in J:
        r = K.mul(r, x[j])
    return r


def check_lemma4(K, n, trials):
    lower = list(subsets(n - 1))
    E = [(S, T) for S in lower for T in lower if S and gt(S, T)]
    for _ in range(trials):
        x = {j: K.rand_nonzero() for j in range(1, n)}
        x[n] = K.rand()
        k = K.rand_nonzero()
        U = random.choice(lower)
        u = {e: K.rand() for e in E}

        def mu(xx, e):
            return K.mul(prod(K, xx, e[0]), K.inv(prod(K, xx, e[1])))

        top = x[n]
        for e in E:
            top = K.add(top, K.mul(u[e], mu(x, e)))
        xt = {j: K.mul(K.pow(k, 2 ** j), x[j]) for j in range(1, n)}
        xt[n] = K.mul(K.pow(k, -s(U)), top)
        # Lemma 4(1)
        for e in E:
            sig = s(e[0]) - s(e[1])
            assert mu(xt, e) == K.mul(K.pow(k, sig), mu(x, e))
        # Lemma 4(2)
        ell = {e: K.rand() for e in E}
        U1 = random.choice(lower)
        lhs = xt[n]
        for e in E:
            lhs = K.add(lhs, K.mul(ell[e], mu(xt, e)))
        lhs = K.mul(lhs, prod(K, xt, U1))
        rhs = x[n]
        for e in E:
            sig = s(e[0]) - s(e[1])
            coef = K.add(u[e], K.mul(ell[e], K.pow(k, sig + s(U))))
            rhs = K.add(rhs, K.mul(coef, mu(x, e)))
        rhs = K.mul(K.mul(K.pow(k, s(U1) - s(U)), rhs), prod(K, x, U1))
        assert lhs == rhs
        # Lemma 4(3)
        i = random.randrange(1, n)
        T = random.choice([T for T in subsets(i - 1)])
        SS = [S for S in subsets(i - 1) if S and gt(S, T)]
        a = s(T | {i})
        ellS = {S: K.rand() for S in SS}
        lhs = K.mul(xt[i], prod(K, xt, T))
        rhs = K.mul(x[i], prod(K, x, T))
        for S in SS:
            lhs = K.add(lhs, K.mul(ellS[S], prod(K, xt, S)))
            rhs = K.add(rhs, K.mul(K.mul(ellS[S], K.pow(k, s(S) - a)), prod(K, x, S)))
        assert lhs == K.mul(K.pow(k, a), rhs)
        # exponent positivity sigma_e >= 2
        assert all(s(S) - s(T) >= 2 for (S, T) in E)


def check_blocks(trials):
    for _ in range(trials):
        n = random.randrange(2, 7)
        a = [random.randrange(1, 5) for _ in range(n)]
        F = sum(a) + random.randrange(0, 4)
        N1 = F + n
        iota = sorted(random.sample(range(1, 10 * N1), N1))
        b = [0]
        for h in range(n):
            b.append(b[-1] + a[h] - 1)
        B = [frozenset(iota[j - 1] for j in range(b[i] + 1, b[i + 1] + 1)) for i in range(n)]
        pi = [iota[F + n + 1 - (i + 1) - 1] for i in range(n)]
        D = [B[i] | {pi[i]} for i in range(n)]
        assert all(len(D[i]) == a[i] for i in range(n))
        for Q in itertools.chain.from_iterable(itertools.combinations(range(n), m) for m in range(1, n + 1)):
            i0 = min(Q)
            assert all(t < pi[i0] for t in B[i0])
            for i in Q:
                if i == i0:
                    continue
                assert D[i] and max(D[i]) < pi[i0] and gt(D[i], B[i0])


def main():
    fields = [Fp(2), Fp(3), Fp(5), Fp(1000003), Fp(2305843009213693951), GF256()]
    for K in fields:
        for n in (2, 3, 4):
            check_lemma4(K, n, 40 if n < 4 else 10)
    check_blocks(300)
    print("identity_check: PASS (random evaluation; not a proof)")


if __name__ == "__main__":
    sys.exit(main())
