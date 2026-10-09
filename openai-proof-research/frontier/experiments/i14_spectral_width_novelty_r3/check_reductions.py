"""Exact prior-art coefficient reduction. Polynomial arithmetic copied from the frozen R2 diagnostic; standard library only."""
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
def ck(name, residual):
    assert not residual.terms, (name, residual.terms)
    checks.append({"name":name,"residual_coefficients":0})
q,a,b,mu,z,X,Y,aa,ab,ac,k,m,hp,mpp = variables("q a beta mu z X Y aa ab ac k m hp mpp")
# q=a/2; multiply both sides by all stated nonzero denominators.
ck("CS_pressure_twice_equals_candidate", 2*(3-a*F(1,2))*(8-a)-2*(6-a)*(4-a*F(1,2)))
ck("CS_surface_gradient_equals_4_over_gamma_surface", 8*(2-a*F(1,4))-4*(4-a*F(1,2)))
ck("CS_HKKZ_length_scale_squared", 2*(4-a*F(1,2))*(6-a)-2*(8-a)*(3-a*F(1,2)))
ck("CS_tangential_completion_cleared",4*(4-q)*(X*X+q*z*Y*X+(q*q*F(1,4)-q)*z*z*Y*Y)-(16*X*X-q*((4-q)*z*Y-2*X)**2))
ck("CS_normal_completion_cleared",4*(4-q)*(F(3,4)*(mu-q*z)**2+q*(mu-q*z)*z+q*z*z)-(q*((4-q)*z-mu)**2+4*(3-q)*mu*mu))
H=aa+ac; norm=aa*aa+2*ab*ab+ac*ac; norm0=(aa-ac)**2*F(1,2)+2*ab*ab;Q=-norm+(1-b)*H*H
ck("seam_tracefree_identity",Q+norm0+(b-F(1,2))*H*H)
ck("source_mollifier_seam_gain",(k*k-1)*Q-(1-k*k)*(norm0+(b-F(1,2))*H*H))
ck("collar_normal_cancellation",-norm-H*H-2*hp+2*(hp-mpp)+2*H*(H-m)-b*(H-m)**2-(-norm-m*m-2*mpp+(1-b)*(H-m)**2))
gam=P.variable("gamma");d=2*gam-1
ck("index_completion",4*d*(X*X-z*Y*X-F(1,4)*d*z*z*Y*Y)-(8*gam*X*X-(d*z*Y+2*X)**2))
ck("endpoint_general_warp",6*(z+X*X)-4*z-6*X*X-2*z)
result={"status":"PASS","exact_identities":len(checks),"checks":checks,"python":sys.version,"script_sha256":hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),"method":"coefficientwise rational polynomial arithmetic, denominators cleared, no parameter sampling","domains":["2 <= q=a/2 < 3", "gamma_surface=(4-q)/2 > 1/2", "beta=2/q > 2/3", "seam gain nonnegative for beta>=1/2 and |k|<=1"],"limitation":"Formal identities do not certify global geometry or research significance."}
Path(__file__).with_name("reduction-checks.json").write_text(json.dumps(result,indent=2)+"\n")
print(json.dumps(result,indent=2))
