#!/usr/bin/env python3
"""I38 finite algebra checks and deterministic floating diagnostics; not a proof audit.

Standard library only. Does not change sources, seals, or expected results.
"""
import json
import math
from fractions import Fraction as F


class Poly(dict):
    """Sparse exact rational polynomials in three formal variables."""
    def __add__(self, other):
        if not isinstance(other, Poly):
            other = Poly({(0, 0, 0): F(other)})
        out = Poly(self)
        for m, c in other.items():
            out[m] = out.get(m, F(0)) + c
        return Poly({m: c for m, c in out.items() if c})
    __radd__ = __add__
    def __neg__(self):
        return Poly({m: -c for m, c in self.items()})
    def __sub__(self, other):
        return self + (-other)
    def __rsub__(self, other):
        return -self + other
    def __mul__(self, other):
        if not isinstance(other, Poly):
            other = Poly({(0, 0, 0): F(other)})
        out = Poly()
        for m, c in self.items():
            for n, d in other.items():
                key = tuple(x+y for x, y in zip(m, n))
                out[key] = out.get(key, F(0)) + c*d
        return Poly({m: c for m, c in out.items() if c})
    __rmul__ = __mul__
    def __pow__(self, n):
        out = Poly({(0, 0, 0): F(1)})
        for _ in range(n):
            out = out*self
        return out


def exact_checks():
    a, b, c = [Poly({tuple(int(i == j) for i in range(3)): F(1)}) for j in range(3)]
    results = {}
    def check(name, condition):
        assert condition, name
        results[name] = "PASS"
    # c = sqrt(3) times the off-diagonal entry of the 2x2 shape matrix.
    edges = [2*a, F(1, 2)*a+F(3, 2)*b+c, F(1, 2)*a+F(3, 2)*b-c]
    check("triangle_trace", sum(edges) == 3*(a+b))
    check("triangle_anisotropy_identity", sum((edges[i]-edges[j])**2 for i in range(3) for j in range(i)) == F(9, 2)*(a-b)**2+6*c**2)
    s, q, r = a+b+c, a*b+a*c+b*c, a*b*c
    coeff = sum((1+x)**2*(1+y)**2 for x, y in [(a,b),(a,c),(b,c)])
    check("residual_coefficient_expansion", coeff == 3+4*s+2*s**2+2*s*q+q**2-(6+2*s)*r)
    check("residual_coefficient_88_over_9", 3+4+2+F(2,3)+F(1,9) == F(88,9) < 10)
    check("simplex_q_bound_identity", s**2-3*q == F(1,2)*((a-b)**2+(a-c)**2+(b-c)**2))
    # PSD eigenvalues: fourth moment=(sum lambda)^2+2 sum lambda^2.
    check("gaussian_fourth_trace_slack", 3*s**2-(s**2+2*(a*a+b*b+c*c)) == 4*q)
    check("gaussian_cube_constant", F(3)**3 < F(5,2)**4 and 27 > 16)
    # Triangle integral over p,q>=0, p+q<=3s: integral (3s-p-q)= (3s)^3/6.
    check("pair_simplex_integral_coefficient", F(27)*(F(1,2)-F(1,3)) == F(27,6))
    check("pair_determinant_coefficient_after_B_cancellation", F(27,6)*2/F(2)/F(3,2) == 3)
    check("radial_cubic_integral", F(1,2)-F(1,3) == F(1,6))
    check("radial_constant", F(1,6)/F(1,192) == 32 and 32*12 == 384 < 400)
    check("activation_normalization_budget", F(400,1600) == F(1,4))
    check("triangle_remainder_constant", F(9,2)/8/6 == F(3,32))
    check("score_stability_constant", F(3,64)/2 == F(3,128) and F(3,8) > F(3,64))
    check("margin_optimization", F(1,18)*(1-F(9,18)) == F(1,36))
    # z is cos(t); coefficients represent pi times the sector deficit.
    check("sector_deficit_identity", F(9,8)-(F(7,4)+a*F(1,2))*F(1,2) == (1-a)*F(1,4))
    check("sector_asymptotic_ratio_over_pi", F(1,8)/F(1,4) == F(1,2))
    # t^2 W(tx) has integral exponent 2p-1=2gamma, for p=gamma+1/2.
    check("LT_normalizing_exponent", 2*(a+F(1,2))-1 == 2*a)
    return results


def simpson(f, low, high, n):
    assert n % 2 == 0
    step = (high-low)/n
    return step/3*(f(low)+f(high)+sum((4 if j%2 else 2)*f(low+j*step) for j in range(1,n)))


def floating_checks():
    """Independent orthogonal equal-norm tails; fixed total tail energy E.

    Activation integral after conditioning on the planar angle:
    sigma int_0^infty [1-Phi(t)^m][1-exp(-sigma^2*t^2/(2*q(theta)^2))] dt.
    Truncate at t=12 and Simpson integrate. No certified error is asserted.
    """
    rows = []
    for m in [1, 4, 32, 1024]:
        for energy in [1e-3, 1e-4, 1e-6, 1e-8]:
            sigma = math.sqrt(energy/m)
            def angular(theta):
                q = math.sqrt((1-energy)/3)*math.cos(theta)
                def f(t):
                    tail = math.erfc(t/math.sqrt(2))/2
                    survival = -math.expm1(m*math.log1p(-tail))
                    radius_cdf = -math.expm1(-sigma*sigma*t*t/(2*q*q))
                    return sigma*survival*radius_cdf
                return simpson(f, 0, 12, 480)
            gain = (3/math.pi)*simpson(angular, 0, math.pi/3, 80)
            rows.append({"extra_labels":m,"tail_energy":energy,"activation_over_energy_3_over_2":round(gain/energy**1.5,10),"status":"floating diagnostic only"})
    return rows


if __name__ == "__main__":
    print(json.dumps({"exact_checks":exact_checks(),"floating_activation":floating_checks(),"scope":"Finite algebra diagnostics, not a universal proof or independent review."},indent=2))
