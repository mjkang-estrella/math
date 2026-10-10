"""Finite rational diagnostics only; not universal analytic certification."""
from fractions import Fraction as F
from math import comb, factorial
import runpy


def run():
    counts = {}
    count = 0
    for t in [F(1,10), F(1,4), F(1,2), F(3,4), F(9,10)]:
        for r in [F(1,4), F(1), F(3)]:
            R = r + F(1,2)
            joint = R*(1-2*t)**2/(4*t*(1-t))
            product = R*((1-t)/(4*t)+t/(4*(1-t)))
            assert product-joint == R/2
            A = F(5,8)/(1-t)+joint
            D = 4*(A+1)
            assert 2*A/D <= F(1,2)
            assert A > 0 and D > 4
            count += 1
    counts['weyl_noise_and_thermal_exponents'] = count
    count = 0
    for j in range(2,35):
        eps = F(1,4**j)
        m = j
        assert F(2**m)**2*eps == 1
        for bq in [F(0), F(1,7), F(5), F(100)]:
            for amp in [F(1), F(3), F(1000)]:
                lhs = bq/F(2**m)+(2**m-1)*eps*amp
                rhs = (bq+2)*amp/F(2**j)
                assert lhs <= rhs
                count += 1
    counts['dyadic_error_budgets'] = count
    count = 0
    for n in range(1,9):
        for K in range(0,65):
            assert comb(K+n,n) <= (K+1)**n
            count += 1
        for lam in [F(4),F(8),F(16),F(32),F(100)]:
            # One positive term of exp(lambda/2) pays W5's polynomial.
            term = (lam/2)**(n+3)/factorial(n+3)
            assert lam**(n+2)/term == F(2**(n+3)*factorial(n+3),1)/lam
            count += 1
    counts['rank_and_exponential_series_budgets'] = count
    count = 0
    for k in range(1,32):
        for p in [F(1,100),F(1,7),F(1,2),F(1)]:
            probs = [F(0)]*(k+2)
            probs[0] = 1-p
            probs[k] += p
            comm = sum(j*(probs[j]-probs[j-1])**2 for j in range(1,k+2))
            energy = k*p
            assert comm <= 4*energy+2
            count += 1
    counts['finite_diagonal_commutator_energy_cases'] = count
    count = 0
    for p in [F(1,8),F(1,32),F(1,128),F(1,512)]:
        for c in [F(1,7),F(1),F(5)]:
            # Work in coefficients of a_p, avoiding irrational square roots.
            assert (1-p)*(-p)+p*(1-p) == 0
            a2 = c/(p*(1-p))
            assert ((1-p)*p*p+p*(1-p)**2)*a2 == c
            assert p*p*a2 == c*p/(1-p)
            for r in [F(1,4),F(1),F(7)]:
                assert a2/(4*(r+1)) == c/(4*(r+1)*p*(1-p))
                count += 1
    counts['centered_satellite_energy_and_tail_exponents'] = count
    old = runpy.run_path('frontier/experiments/i117_bosonic_entropy_stability/check.py')
    logs = old['log_bounds']
    count = 0
    for r in [F(1,4),F(1),F(3),F(7)]:
        for b in [F(1,8),F(1,2),F(2),F(9)]:
            for eta in [F(1,10),F(1,3),F(1,2),F(9,10)]:
                s = eta*r+(1-eta)*b
                hr = logs(1+1/r)
                hs = logs(1+1/s)
                assert eta*hs[1] < hr[0]
                count += 1
    counts['strict_baseline_sign_rational_log_enclosures'] = count
    count = 0
    for q1 in [F(1,3),F(1,2),F(3,4)]:
        for q2 in [F(1,4),F(2,3)]:
            for d0,d1,d2 in [(F(8),F(2),F(1,10)),(F(4),F(1),F(0))]:
                assert d1 <= q1*d0 and d2 <= q2*d1
                assert q1*q2*d0-d2 == q2*(q1*d0-d1)+(q2*d1-d2)
                count += 1
    counts['stieltjes_finite_partition_telescope'] = count
    return dict(status='PASS', counts=counts,
                scope='Finite exact rational checks and rigorous logarithm enclosures; no universal proof or substantiality certification')


if __name__ == '__main__':
    import json
    print(json.dumps(run(), indent=2, sort_keys=True))
