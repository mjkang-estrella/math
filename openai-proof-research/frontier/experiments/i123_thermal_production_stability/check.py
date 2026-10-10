"""Finite exact arithmetic diagnostics, not proofs of operator inequalities."""
from fractions import Fraction as F
from math import comb


def run():
    counts = {}
    count = 0
    for y in [F(1,8), F(1,2), F(1), F(4), F(32)]:
        q = 2*y/(2*y+1)
        for n in range(1,6):
            g = ((y+1)*(1+1/(2*y)))**(-n)
            for L in [0,1,4,16,64]:
                inverse = ((y+1)*(1+1/(2*y)))**n*(1+1/(2*y))**L
                assert inverse*g*q**L == 1
                assert 0 < g < 1 and 0 < q < 1
                if y == F(1,2):
                    assert inverse == 3**n*2**L
                count += 1
    counts['variable_instrument_and_original_specialization'] = count
    count = 0
    for t in [F(1,5),F(1,2),F(4,5)]:
        for y in [F(1,2),F(1),F(4),F(32)]:
            for Q in [F(1),F(4),F(16)]:
                for L in [1,4,16,64]:
                    aa=y*Q*Q/(2*(1-t)); bb=F(L)/(8*y)
                    assert (aa+bb)**2 >= Q*Q*L/(4*(1-t))
                    assert F(1)/(2*y+1) >= F(1)/(4*y)
                    A_noise=(2*y+F(3,2))/(4*(1-t))
                    assert A_noise >= y/(2*(1-t))
                    if y==F(1,2):
                        assert A_noise==F(5,8)/(1-t)
                    count += 1
    counts['filter_frequency_cost_tradeoff'] = count
    count = 0
    for n in range(1,6):
        for r in [F(1,4),F(1),F(3)]:
            for x in [r,r+F(1,8),r+1]:
                # Formal BV chain coefficients in independent variables
                # G=g(x)-g(r), H=h(x), dx=(r-x)dv+exp(-v)dnu.
                for G in [F(0),F(1,3),F(2)]:
                    for H in [F(1,8),F(1),F(3)]:
                        k=n*(G+(r-x)*H)
                        assert n*G+n*H*(r-x)==k
                        # k'=n*(h-h+(r-x)h'), h'=-1/(x(x+1)).
                        assert n*(r-x)*(-1/(x*(x+1))) == n*(x-r)/(x*(x+1))
                        count += 1
    counts['formal_stieltjes_product_chain_coefficients'] = count
    count = 0
    for T in [F(1,10),F(1),F(10)]:
        for C2 in [F(1,4),F(1),F(20)]:
            for d in [F(0),F(1,10),F(1),F(2)]:
                h0=min(T,d*d/(4*C2))
                assert h0 >= d*d*min(T,1/C2)/4
                count += 1
    counts['conditional_power_short_time_constant'] = count
    count = 0
    for q in [F(1,8),F(1,2),F(7,8)]:
        for r in [F(1,4),F(1),F(3)]:
            for k in [0,1,2,8,64]:
                f2=q*q*k*(k-1)+4*q*(1-q)*r*k+2*(1-q)**2*r*r
                assert f2>=q*q*k*(k-1)
                count += 1
    counts['nonnegative_number_factorial_moment_terms'] = count
    count = 0
    for n in range(1,8):
        for K in range(33):
            assert comb(K+n,n)<=(K+1)**n
            count += 1
    counts['number_cutoff_ranks'] = count
    return dict(status='PASS',counts=counts,
                scope='Finite exact rational/formal coefficient diagnostics only; no universal proof, rate, or substantiality certification')


if __name__ == '__main__':
    import json
    print(json.dumps(run(),indent=2,sort_keys=True))
