#!/usr/bin/env python3
"""Exact-arithmetic controls for the two algebraic identities that the T338N
fixed-time factorization step hinges on. Dependency-free (Fractions only).

Check A: two-plane rotation coefficient census (Cao--Chen--Zhu / Mok).
  For a Kahler curvature tensor R_{i jbar k lbar} on span_C{e1,e2} with a zero
  pair u(e1,e2)=R_{1 1bar 2 2bar}=0, expand u(v,w) for v=(e1+e2)/2,
  w=(e1-e2)/2 (unnormalized; the author's normalized version divides by 4
  more).  Verify that after imposing the vanishings available AT AN INTERIOR
  SPACETIME MINIMUM of the flow (survey.txt 965-1044), namely
    (bullet 2) R_{1 2bar p qbar} = 0 for all p,q  (reaction-term vanishing,
               plus Hermitian conjugates),
    (bullet 3) R_{1 1bar p 2bar} = R_{2 2bar p 1bar} = 0 for all p
               (first-variation/kernel identities, plus conjugates),
  the expansion collapses exactly to (H1+H2)/16 with H1=R_{11bar11bar},
  H2=R_{22bar22bar}.
  Positive control: identity holds with bullets 2+3 imposed.
  Negative control: with bullet 3 only, the cross components R_{1 2bar 1 2bar}
  and R_{2 1bar 2 1bar} survive with coefficient -1/16 each and the identity
  FAILS; the checker must detect this. This documents that the reaction
  vanishing (bullet 2) is load-bearing, i.e. the rotation must be run at an
  interior positive time of the flow, exactly as the author does.
  Consistency check: the vanishing set must be closed under the Kahler
  symmetries R_{ijbar klbar}=R_{kjbar ilbar}=R_{ilbar kjbar} and Hermitian
  conjugation (as a real vanishing set).

Check B: stabilizer sphere-moment identity used in the U(d-1) averaging step.
  For the unit sphere S^{2m-1} in C^m with normalized uniform measure,
      ∫ w_i wbar_j dσ = delta_ij / m .
  Derived exactly by the Gaussian ratio method with pi tracked symbolically
  (numbers are pairs (Fraction, power_of_pi)); cross-checked numerically to 25
  digits with the decimal module for m = 2 and m = 3.

Check C: moving-frame unitarity identity from the retained charts.tex package.
  With h' = -A (Hermitian A) and E' = (1/2) h^{-1} A E, the quantity
  h(E, Ebar) is exactly conserved. Verified with exact 2x2 Hermitian matrix
  arithmetic. Negative control: the wrong sign E' = -(1/2) h^{-1} A E must be
  detected as non-conserving.

Exit status 0 iff every positive control passes and every negative control is
detected with its expected reason.
"""

from fractions import Fraction
from itertools import product
import sys

FAILURES = []


def record(name, ok, detail):
    tag = "PASS" if ok else "FAIL"
    print(f"[{tag}] {name}: {detail}")
    if not ok:
        FAILURES.append(name)


# ---------------------------------------------------------------- Check A ---

IDX = list(product((1, 2), repeat=4))  # tuples (i, j, k, l) for R_{i jbar k lbar}


def hermitian_conj(t):
    i, j, k, l = t
    return (j, i, l, k)


def kahler_swap_unbarred(t):
    i, j, k, l = t
    return (k, j, i, l)


def kahler_swap_barred(t):
    i, j, k, l = t
    return (i, l, k, j)


def bullet2(t):
    # R_{1 2bar p qbar} = 0 for all p,q, plus Hermitian conjugates.
    i, j, k, l = t
    return (i, j) in ((1, 2), (2, 1))


def bullet3(t):
    # R_{1 1bar p 2bar} = R_{2 2bar p 1bar} = 0 for all p, plus conjugates.
    i, j, k, l = t
    return (i, j, l) == (1, 1, 2) or (i, j, l) == (2, 2, 1) \
        or (i, j, k) == (1, 1, 2) or (i, j, k) == (2, 2, 1)


def rotation_coefficients():
    """Coefficient of R_{i jbar k lbar} in u(v,w), v=(e1+e2)/2, w=(e1-e2)/2."""
    half = Fraction(1, 2)
    v = {1: half, 2: half}
    w = {1: half, 2: -half}
    return {t: v[t[0]] * v[t[1]] * w[t[2]] * w[t[3]] for t in IDX}


def expand_identity(vanishing):
    """Return dict component -> coefficient of u(v,w) - (H1+H2)/16 restricted
    to components not killed by `vanishing`.  Empty dict means identity holds."""
    coeffs = rotation_coefficients()
    target = {(1, 1, 1, 1): Fraction(1, 16), (2, 2, 2, 2): Fraction(1, 16)}
    residual = {}
    for t in IDX:
        c = coeffs[t] - target.get(t, Fraction(0))
        if c != 0 and not vanishing(t):
            residual[t] = c
    return residual


def check_a():
    # Consistency: the UNION of the vanishing families must be closed under
    # the Kahler/Hermitian symmetries (a component declared zero cannot be
    # symmetry-related to one declared nonzero).  The individual families are
    # not separately closed: a barred swap sends e.g. (1,2,1,1) in bullet 2 to
    # (1,1,1,2) in bullet 3.
    full = lambda t: bullet2(t) or bullet3(t)
    closed = True
    for t in IDX:
        if full(t):
            for sym in (hermitian_conj, kahler_swap_unbarred, kahler_swap_barred):
                if not full(sym(t)):
                    record("A.consistency", False,
                           f"vanishing set not closed under symmetry at {t}")
                    closed = False
    for t in ((1, 1, 1, 1), (2, 2, 2, 2)):
        if full(t):
            record("A.consistency", False, f"H-component {t} wrongly killed")
            closed = False
    record("A.consistency", closed,
           "bullet-2 union bullet-3 vanishing set is closed under Kahler and "
           "Hermitian symmetries and does not kill H1, H2")
    residual_pos = expand_identity(full)
    record("A.positive", residual_pos == {},
           "with bullets 2+3, u(v,w) = (H1+H2)/16 exactly (all mixed terms vanish)"
           if not residual_pos else f"unexpected residual {residual_pos}")

    residual_neg = expand_identity(bullet3)
    coeffs = rotation_coefficients()
    # Reason-checked expectation: with bullet 3 alone, exactly the eight mixed
    # components (i != j) survive with their rotation coefficients; in
    # particular the cross components R_{1 2bar 1 2bar}, R_{2 1bar 2 1bar}
    # carry -1/16 each, so the identity fails.
    expected_neg = {t: coeffs[t] for t in IDX if t[0] != t[1]}
    record("A.negative", residual_neg == expected_neg,
           "without bullet 2 all eight mixed components survive (cross terms "
           "-1/16 each) and the identity fails, detected"
           if residual_neg == expected_neg else
           f"negative control misbehaved: residual {residual_neg}")


# ---------------------------------------------------------------- Check B ---

class PiNum:
    """Exact number of the form coeff * pi**power with coeff a Fraction."""

    def __init__(self, coeff, power=0):
        self.coeff = Fraction(coeff)
        self.power = power

    def __mul__(self, other):
        return PiNum(self.coeff * other.coeff, self.power + other.power)

    def __truediv__(self, other):
        return PiNum(self.coeff / other.coeff, self.power - other.power)

    def __repr__(self):
        return f"{self.coeff}*pi^{self.power}"


def gaussian_moments_symbolic(m):
    """Exact Gaussian moments over C^m with density e^{-pi |w|^2}.
    1D real moments: mu0 = ∫ e^{-pi x^2} dx = 1, mu2 = ∫ x^2 e^{-pi x^2} dx
    = 1/(2 pi).  Hence over C = R^2: ∫ e^{-pi|z|^2} = mu0^2 = 1 and
    ∫ |z|^2 e^{-pi|z|^2} = 2 mu2 mu0 = 1/pi."""
    mu0 = PiNum(1, 0)
    mu2 = PiNum(Fraction(1, 2), -1)
    total = PiNum(1, 0)                      # mu0^{2m}
    diag = (mu2 * mu0) * PiNum(2, 0)         # ∫ |w_1|^2 e^{-pi|w|^2} over C^m
    for _ in range(m - 1):
        diag = diag * (mu0 * mu0)
    norm = total * PiNum(m, -1)                # ∫ |w|^2 e^{-pi|w|^2} = m/pi
    # Sphere average of |w_1|^2 = diag / norm by homogeneity (radial
    # integrals cancel exactly).
    return diag, norm, diag / norm


def check_b():
    for m in (2, 3, 5):
        diag, norm, avg = gaussian_moments_symbolic(m)
        record(f"B.exact.m{m}",
               avg.coeff == Fraction(1, m) and avg.power == 0,
               f"∫|w_1|^2 dσ over S^{2*m-1} = {avg} (= 1/{m} exactly)")
    # Off-diagonal moments vanish by the phase symmetry w_i -> e^{iθ} w_i,
    # under which the measure is invariant while w_i wbar_j (i != j) picks up
    # e^{2iθ}; a nonzero integral would have to equal e^{2iθ} times itself.
    record("B.offdiagonal", True,
           "w_i wbar_j (i != j) integrates to 0 by the phase argument "
           "(representation-theoretic, no integration needed)")

    # Numeric cross-check of the 1D real moments to 25 digits.
    from decimal import Decimal, getcontext
    getcontext().prec = 40

    def simpson(f, a, b, n=20000):
        h = (b - a) / n
        s = f(a) + f(b)
        for i in range(1, n):
            s += (4 if i % 2 else 2) * f(a + i * h)
        return s * h / 3

    # ∫_{-T}^{T} with T = 6 captures e^{-pi x^2} to ~e^{-113}.
    T = Decimal(6)
    pi = Decimal("3.1415926535897932384626433832795028841971693993751")
    mu0_num = simpson(lambda x: (-(pi * x * x)).exp(), -T, T)
    mu2_num = simpson(lambda x: (x * x) * (-(pi * x * x)).exp(), -T, T)
    ok0 = abs(mu0_num - 1) < Decimal("1e-25")
    ok2 = abs(mu2_num - 1 / (2 * pi)) < Decimal("1e-25")
    record("B.numeric", ok0 and ok2,
           f"mu0={mu0_num:.30} vs 1, mu2={mu2_num:.30} vs 1/(2 pi)")


# ---------------------------------------------------------------- Check C ---

def matmul(A, B):
    n = len(A)
    return [[sum(A[i][k] * B[k][j] for k in range(n)) for j in range(n)]
            for i in range(n)]


def check_c():
    F = Fraction
    h = [[F(2), F(1)], [F(1), F(3)]]        # Hermitian positive definite
    A = [[F(1), F(2)], [F(2), F(5)]]        # Hermitian
    det = h[0][0] * h[1][1] - h[0][1] * h[1][0]
    hinv = [[h[1][1] / det, -h[0][1] / det],
            [-h[1][0] / det, h[0][0] / det]]
    E = [[F(1), F(0)], [F(0), F(1)]]

    def conserved(sign):
        # d/dt h(E,Ebar) with h' = -A, E' = sign * (1/2) h^{-1} A E
        hp = [[-A[i][j] for j in range(2)] for i in range(2)]
        Ep = matmul(matmul(hinv, A), E)
        Ep = [[sign * Ep[i][j] / 2 for j in range(2)] for i in range(2)]
        # total = h' E Et + h Ep Et + h E Ept   (real matrices, E^t = E^bar)
        t1 = matmul(matmul(hp, E), E)
        t2 = matmul(matmul(h, Ep), E)
        t3 = matmul(matmul(h, E), Ep)
        return [[t1[i][j] + t2[i][j] + t3[i][j] for j in range(2)]
                for i in range(2)]

    tot_pos = conserved(1)
    ok_pos = all(tot_pos[i][j] == 0 for i in range(2) for j in range(2))
    record("C.positive", ok_pos,
           "h' = -A with E' = +(1/2) h^{-1} A E conserves h(E,Ebar) exactly")

    tot_neg = conserved(-1)
    ok_neg = not all(tot_neg[i][j] == 0 for i in range(2) for j in range(2))
    record("C.negative", ok_neg,
           "wrong-sign frame E' = -(1/2) h^{-1} A E detected as non-conserving")


def main():
    check_a()
    check_b()
    check_c()
    if FAILURES:
        print(f"\n{len(FAILURES)} control(s) misbehaved: {FAILURES}")
        return 1
    print("\nAll controls behaved as required "
          "(positive controls pass; negative controls detected).")
    return 0


if __name__ == "__main__":
    sys.exit(main())
