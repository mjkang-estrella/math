"""Formal polynomial diagnostics for I14 R2; Python standard library only.

All equalities are coefficientwise identities in rational polynomial rings,
after explicitly clearing nonzero denominators. No sampling is used.
Geometric existence, positivity domains, and topology are proved in the review.
Run from any directory: python /absolute/path/to/this/check.py
"""
from fractions import Fraction as F
from pathlib import Path
import hashlib
import json
import sys


class P:
    def __init__(self, terms=0):
        self.terms = ({(): F(terms)} if terms else {}) if not isinstance(terms, dict) else {
            k: F(v) for k, v in terms.items() if v
        }

    @staticmethod
    def variable(name):
        return P({((name, 1),): F(1)})

    def __add__(self, other):
        other = other if isinstance(other, P) else P(other)
        result = self.terms.copy()
        for key, val in other.terms.items():
            result[key] = result.get(key, F(0)) + val
        return P(result)

    __radd__ = __add__

    def __neg__(self):
        return P({k: -v for k, v in self.terms.items()})

    def __sub__(self, other):
        return self + (-other)

    def __rsub__(self, other):
        return -self + other

    def __mul__(self, other):
        other = other if isinstance(other, P) else P(other)
        result = {}
        for k, v in self.terms.items():
            for l, w in other.terms.items():
                powers = dict(k)
                for name, power in l:
                    powers[name] = powers.get(name, 0) + power
                key = tuple(sorted(powers.items()))
                result[key] = result.get(key, F(0)) + v*w
        return P(result)

    __rmul__ = __mul__

    def __pow__(self, n):
        assert isinstance(n, int) and n >= 0
        out = P(1)
        for _ in range(n):
            out = out*self
        return out


def variables(names):
    return [P.variable(name) for name in names.split()]


checks = []


def zero(name, residual, domain="all real variables"):
    assert not residual.terms, (name, residual.terms)
    checks.append({"name": name, "residual_coefficients": 0, "domain": domain})


b, gam, a, v, mu, eta, nmu = variables("beta gamma a normal_T mu eta normal_mu")
x1, x2, p1, p2 = variables("T1 T2 p1 p2")
X, Y, C = x1*x1+x2*x2, p1*p1+p2*p2, x1*p1+x2*p2
R, ric, hess, lapT, B2 = variables("R Ric Hess lapT B2")
H = mu+v
lapP = C-ric-hess-B2-nmu-Y-eta
Dambient = R+2*(lapT+H*v+hess)-b*(X+v*v)
Dsurface = R-2*ric+H*H-B2+2*lapT-2*lapP-gam*(X-2*C+Y)
rhs = Dambient+(b-gam)*X+2*(gam-1)*C+(2-gam)*Y+mu*mu+(b-1)*v*v+B2+2*nmu+2*eta
zero("full_Gauss_Jacobi_transfer_including_eigenvalue_remainder", Dsurface-rhs)
G = 2*b-1  # gamma = G / beta
zero("tangential_square_after_multiplication_by_beta",
     (b*b-G)*X+2*(G-b)*C+(2*b-G)*Y-
     ((p1+(b-1)*x1)**2+(p2+(b-1)*x2)**2), "beta != 0")
normal = mu*mu+(b-1)*v*v+F(1,2)*(mu+v)**2
zero("normal_square_after_multiplication_by_2_times_2beta_minus_1",
     2*(2*b-1)*normal-((2*b-1)*v+mu)**2-2*(3*b-2)*mu*mu,
     "2 beta - 1 != 0")
z, psi, dpsi = variables("Uprime psi dpsi")
d = 2*gam-1
zero("index_square_after_multiplication_by_4_times_2gamma_minus_1",
     4*d*(dpsi*dpsi-z*psi*dpsi-F(1,4)*d*z*z*psi*psi)
     -(8*gam*dpsi*dpsi-(d*z*psi+2*dpsi)**2), "2 gamma - 1 != 0")
zero("gamma_over_2gamma_minus_1_equals_inverse_c",
     G*(3*b-2)-(2*G-b)*(2*b-1), "beta (3 beta - 2) (2 beta - 1) != 0")
zero("c_beta_equals_2_times_6_minus_a_over_8_minus_a",
     (12-2*a)*(8-a)-2*(6-a)*(8-a), "a != 0, a != 8; beta = 4/a")
mp, mpp, hp, aa, ab, ac = variables("mprime msecond Hprime A11 A12 A22")
hh, normA = aa+ac, aa*aa+2*ab*ab+ac*ac
tp, tpp = hh-mp, hp-mpp
original_normal = -normA-hh*hh-2*hp+2*tpp+2*hh*tp-b*tp*tp
collar_normal = -normA-mp*mp-2*mpp+(1-b)*(hh-mp)**2
zero("full_collar_normal_identity", original_normal-collar_normal)
normA0 = F(1,2)*(aa-ac)**2+2*ab*ab
qA = -normA+(1-b)*hh*hh
zero("seam_tracefree_identity_for_arbitrary_symmetric_2_by_2_tensor",
     qA+normA0+(b-F(1,2))*hh*hh)
kappa = P.variable("kappa")
zero("seam_average_gain",
     (kappa*kappa-1)*qA-(1-kappa*kappa)*(normA0+(b-F(1,2))*hh*hh),
     "gain >= 0 for beta >= 1/2 and abs(kappa) <= 1")
u, Lu, du2 = variables("u Lap_u grad_u_squared")
# Multiply 2 Delta T - beta |dT|^2 + a Delta u/u by u^2,
# with T=-(a/2)log u and beta=4/a.
zero("groundstate_to_D_beta", -a*(u*Lu-du2)-a*du2+a*u*Lu, "u > 0, a > 0")
m, q, qp, t = variables("m q qprime t")
scal = -2*m*qp-m*(m+1)*q*q
Lu_over_u = -F(1,2)*m*qp-F(1,4)*m*m*q*q
zero("general_warped_endpoint_after_multiplication_by_m",
     m*scal-4*(m+1)*Lu_over_u-2*m*qp, "m > 0, a = 4(m+1)/m")
zero("three_dimensional_endpoint", (-8-24*t*t)-6*(-2-4*t*t)-4)
s, width, cot, pi, grad_rho = variables("s width cot pi grad_rho")
# d_mu/d_rho = -s*pi/width * (1+cot^2); mu = s*cot.
zero("pressure_derivative_form_after_multiplication_by_width_times_s_squared",
     -s*s*s*pi*(1+cot*cot)+s*pi*(s*s+(s*cot)**2), "s > 0, width > 0")
zero("pressure_curvature_reserve",
     F(1,2)+cot*cot-F(1,4)*(1+cot*cot)-F(1,4)-F(3,4)*cot*cot)

# Uniform numerical inequalities use the classical rational bound pi < 22/7.
pi_upper = F(22,7)
inequalities = {
    "exit_less_than_detection_radius": 2*pi_upper < 10,
    "pressure_derivative_constant_less_than_quarter": 4*pi_upper/69 < F(1,4),
    "remote_slab_less_than_220": 186+4*pi_upper < 220,
    "near_slab_less_than_220": 204 < 220,
    "whole_fiber_less_than_500": 440+2*(2*pi_upper+2) < 500,
}
assert all(inequalities.values())

here = Path(__file__).resolve().parent
result = {
    "status": "PASS",
    "method": "exact coefficientwise rational polynomial identities; no finite-value sampling",
    "python": sys.version,
    "script_sha256": hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
    "identities": checks,
    "constant_inequalities_using_pi_less_than_22_over_7": inequalities,
    "limitation": "Does not certify minimizers, smoothing convergence, topology, or novelty; see independent written review.",
}
(here/'results.json').write_text(json.dumps(result, indent=2)+'\n')
print(json.dumps({"status": result["status"], "formal_identities": len(checks),
                  "constant_inequalities": len(inequalities)}))
