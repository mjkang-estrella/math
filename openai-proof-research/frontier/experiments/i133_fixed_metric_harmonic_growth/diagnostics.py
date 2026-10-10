"""New finite exact arithmetic only. Does not prove geometry or universal claims."""
from fractions import Fraction as F

def check():
    counts = dict(radial_residual=0, volume_majorant=0, graph_telescoping=0,
                  kernel_norm_factor=0, limiting_mode_count=0, slope_budget=0)
    # Divide L_l(r^l) by l r^l. f/r=x and f'=y.
    for ell in range(1, 41):
        for x in (F(1, 3), F(2, 3), F(9, 10), F(1)):
            for y in (F(1, 3), F(2, 3), F(9, 10), F(1)):
                assert (ell-1)*x*x+2*x*y-(ell+1) <= 0
                counts['radial_residual'] += 1
    # Integrated bound before discarding negative lower-end contributions.
    for a in (F(7, 10), F(4, 5), F(9, 10)):
        for delta in (F(1, 100), F(1, 1000)):
            assert a+delta <= 1
            for R in (F(2), F(10), F(100), F(10000)):
                b = a+delta
                raw = 3/R**3*(F(8, 3)+b*b*(R**3-8)/3+2*b*(R*R-4)+4*(R-2))-a*a
                bound = 2*delta+delta*delta+6/R+12/R**2+8/R**3
                assert raw <= bound
                counts['volume_majorant'] += 1
    # Equality recurrence verifies ordering of the products in (I.3).
    for N in range(1, 31):
        kap = [F(i+1, i+3) for i in range(N)]
        err = [F(1, (i+2)**2) for i in range(N)]
        value = F(3, 7)
        for i in reversed(range(N)):
            value = kap[i]*value+err[i]
        prod = F(1); total = F(0)
        for i in range(N):
            total += prod*err[i]; prod *= kap[i]
        assert value == prod*F(3, 7)+total
        counts['graph_telescoping'] += 1
    # a_l coefficients, with 4*pi removed: exact ball denominator inequality.
    for k in range(21):
        coeff = [F(i+1, 17) for i in range(9)]
        mass = sum(coeff); ball = sum(z/F(2*(k+1+i)+3) for i,z in enumerate(coeff))
        assert mass >= (2*k+5)*ball
        for r in (F(1), F(2), F(10)):
            assert r**(k+1)/(1+r)**k >= r/F(2**k)
        counts['kernel_norm_factor'] += 1
    # Count by an exact inequality, including zero and avoiding sqrt rounding.
    for a2 in (F(1, 2), F(16, 25), F(81, 100)):
        for k in range(1, 101):
            degs = [l for l in range(k+1) if l*(l+1) <= a2*k*(k+1)]
            assert max(degs) <= k-1
            assert sum(2*l+1 for l in degs) == (max(degs)+1)**2 <= k*k
            counts['limiting_mode_count'] += 1
    for N in range(1, 31):
        assert sum(F(1, 2**m) for m in range(1, N+1)) == 1-F(1, 2**N)
        counts['slope_budget'] += 1
    return dict(status='PASS finite exact instances only', instances=counts,
                scope='Arithmetic checks only; no ODE/PDE existence, infinite matching, universal theorem or contribution certification')

if __name__ == '__main__':
    import json
    print(json.dumps(check(), indent=2))
