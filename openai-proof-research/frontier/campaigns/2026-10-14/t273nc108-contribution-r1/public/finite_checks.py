#!/usr/bin/env python3
"""MIT. Independent finite diagnostics only; prints JSON and writes nothing."""
import cmath
from fractions import Fraction as F
import json
import math
import random


def mul(a, b):
    return [[sum(a[i][k] * b[k][j] for k in range(2)) for j in range(2)] for i in range(2)]


def adj(a):
    return [[a[j][i].conjugate() for j in range(2)] for i in range(2)]


def plus(a, b, scale=1):
    return [[a[i][j] + scale * b[i][j] for j in range(2)] for i in range(2)]


def times(c, a):
    return [[c * x for x in row] for row in a]


def diag(a, b):
    return [[a, 0], [0, b]]


def tr(a):
    return a[0][0] + a[1][1]


def norm(a):
    return max(abs(x) for row in a for x in row)


def congr(a, b):
    return mul(mul(a, b), adj(a))


def mineig(a):
    x, y = a[0][0].real, a[1][1].real
    return (x + y - math.sqrt((x-y)**2 + 4 * abs(a[0][1])**2)) / 2


def ell(a, b):
    return a if a == b else (a-b)/(math.log(a)-math.log(b))


def unitary(theta, phase):
    c, s, z = math.cos(theta), math.sin(theta), cmath.exp(1j*phase)
    return [[c, -s*z.conjugate()], [s*z, c]]


def main():
    k = [[F(3,25), F(-12,25)], [F(2,25), F(9,50)]]
    lam = F(1,25)
    h0, h1 = diag(F(1),F(4)), diag(F(1),F(9))
    u = mul(mul(diag(F(5),F(10)),k),diag(F(1),F(1,3)))
    assert mul(adj(k), mul(h0, k)) == times(lam,h1)
    assert mul(adj(u),u) == diag(F(1),F(1))
    naive = sum(k[j][1]**2 for j in range(2))/lam
    assert naive == F(657,100)
    assert u == [[F(3,5),F(-4,5)],[F(4,5),F(3,5)]]

    rng = random.Random(273108)
    residuals = {}
    def check(name, a, b):
        value = norm(plus(a,b,-1))
        residuals[name] = max(residuals.get(name,0),value)
        assert value < 2e-11, (name,value)
    identity = diag(1.,1.)
    positive_min = float('inf')
    transpose_failures = noncommuting = 0
    for index in range(128):
        # Separate physical eigenbases: R and Q diagonal, K and U fully complex.
        hs0 = [rng.uniform(.4,1.1), rng.uniform(1.2,2.)]
        hs1 = [rng.uniform(.7,1.5), rng.uniform(2.2,3.5)]
        h0, h1 = diag(*hs0), diag(*hs1)
        j0, j1 = diag(*[math.sqrt(x) for x in hs0]), diag(*[math.sqrt(x) for x in hs1])
        r = diag(*[1/math.expm1(x) for x in hs1])
        q = diag(*[1/math.expm1(x) for x in hs0])
        u = unitary(rng.uniform(.2,1.3),rng.uniform(.3,2.8))
        lam = 1e-4
        k = times(math.sqrt(lam),mul(mul(diag(*[1/math.sqrt(x) for x in hs0]),u),j1))
        kk = mul(k,adj(k))
        b = plus(q,congr(k,r),-1)
        assert mineig(b)>0 and mineig(plus(identity,kk,-1))>0
        positive_min = min(positive_min,mineig(b),mineig(plus(identity,kk,-1)))
        check('KKT',mul(adj(k),mul(h0,k)),times(lam,h1))
        check('unitarity',mul(adj(u),u),identity)
        check('weighted_transport',mul(j0,k),times(math.sqrt(lam),mul(u,j1)))
        bad_transpose = [[u[j][i] for j in range(2)] for i in range(2)]
        if norm(plus(mul(bad_transpose,u),identity,-1))>1e-3:
            transpose_failures += 1
        if norm(plus(mul(kk,q),mul(q,kk),-1))>1e-8:
            noncommuting += 1
        for theta in [0,1]:
            ref = plus(r,times(theta,identity))
            lhs = plus(mul(h0,plus(q,times(theta,identity))),times(lam,congr(u,mul(h1,ref))),-1)
            rhs = congr(j0,plus(b,times(theta,plus(identity,kk,-1))))
            check('two_congruence_gaps',lhs,rhs)
            assert mineig(plus(mul(h0,plus(q,times(theta,identity))),times(1.01*lam,congr(u,mul(h1,ref))),-1))>0
        z = complex(rng.random(),rng.random())
        x = [[rng.random(),z],[z.conjugate(),rng.random()]]
        check('energy_trace',diag(tr(mul(h0,congr(k,x))),0),diag(lam*tr(mul(h1,x)),0))
        mu = [[complex(rng.random(),rng.random())],[complex(rng.random(),rng.random())]]
        outer = [[mu[i][0]*mu[j][0].conjugate() for j in range(2)] for i in range(2)]
        kout = congr(k,outer)
        alpha, kappa, eps = .93,.07,.03
        m = alpha*lam*tr(mul(h1,outer)).real
        e1 = tr(mul(h1,x)).real
        c0delta = plus(times(alpha,congr(k,x)),times(kappa*alpha,kout))
        e0 = tr(mul(h0,c0delta)).real
        check('mean_and_centered_covariance',diag(e0,0),diag(alpha*lam*e1+kappa*m,0))
        energy_remainder = -e0+(1+eps)*alpha*lam*e1+eps*alpha*lam*(-e1-tr(mul(h1,outer)).real)
        check('cancellation_sign',diag(energy_remainder,0),diag(-(eps+kappa)*m,0))
        qt = math.exp(-rng.uniform(0,5))
        noise = plus(b,times(.5,plus(identity,kk,-1)))
        left = plus(times(1-qt,congr(k,plus(r,times(.5,identity)))),noise)
        right = plus(times(qt,noise),times(1-qt,plus(q,times(.5,identity))))
        check('common_rate_characteristic_exponent',left,right)
        for h in hs0+hs1:
            rj = 1/math.expm1(h)
            p1,p2 = rng.uniform(.01,.9),rng.uniform(.01,.9)
            v = math.log(p1/p2)/h
            bv = v/2/math.tanh(h*v/2) if abs(v)>1e-12 else 1/h
            fw = (bv-(rj+.5)*v)/(1-v)
            check('tilted_logmean',diag(ell(p1,p2)*fw,0),diag(ell(rj*p1,(rj+1)*p2),0))
            d = complex(rng.random(),rng.random())
            raw_dual = abs(d)**2/(h*ell(p1,p2)*fw)
            weighted_dual = abs(math.sqrt(h)*d)**2/(h*ell(p1,p2)*fw)
            check('dual_h_normalization',diag(h*raw_dual,0),diag(weighted_dual,0))
    assert transpose_failures == noncommuting == 128
    print(json.dumps({'status':'FINITE_DIAGNOSTICS_ONLY','seed':273108,'complex_cases':128,
                      'exact_naive_e2_norm_squared':str(naive),
                      'exact_corrected_U':[['3/5','-4/5'],['4/5','3/5']],
                      'noncommuting_cases':noncommuting,'wrong_transpose_detected_cases':transpose_failures,
                      'max_absolute_residuals':residuals,'smallest_tested_positive_gap':positive_min,
                      'limits':'No global Gaussian optimizer, infinite-dimensional theorem, correctness gate, contribution verdict or proof follows from these checks.'},indent=2,sort_keys=True))


if __name__ == '__main__':
    main()
