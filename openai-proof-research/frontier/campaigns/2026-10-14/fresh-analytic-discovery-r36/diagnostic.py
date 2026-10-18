#!/usr/bin/env python3
"""MIT. Exact finite assembly checks, not proof of the local theorem."""
import json
from fractions import Fraction as Q

def main():
    count = 0
    for k in range(4, 201):
        e = Q(1,k)
        R = 1+2/e
        eta = e/(1+e)
        assert eta*(1+e) == e
        assert 2/(R-1) == e
        assert 1/(1+e) >= 1-e
        assert (1+e)**2 <= (1+2*e)/(1-e)
        assert (1+e+e*e)/(1-e) <= (1+2*e)/(1-e)
        assert (1+2*e)/(1-e)**2 <= 1+8*e
        count += 6
    for p in (Q(6,5),Q(3,2),Q(5,2),Q(3),Q(4),Q(20)):
        gamma = 2-p if p<2 else 1-2/p
        assert 0<gamma<1
        count += 1
    e=Q(1,4); ratio=1+e
    levels=[]; x=ratio
    while x<e**(-2):
        levels.append(x);x*=ratio
    levels.append(x)
    M=len(levels)
    # Actual rational bins at extreme scales, with shared closed endpoints.
    for d in (Q(1,10**1000),Q(1),Q(10**1000)):
        bins=[(e*d*t/ratio,e*d*t) for t in levels]
        assert bins[0][0]==e*d
        assert bins[-1][1]>=d/e
        assert all(bins[j][1]==bins[j+1][0] for j in range(M-1))
        count += M+1
    controls={
        # For T={0,2}, x=1 in real L4, unconditional radial extension
        # has distance fourth power17 to terminal2, while true distance=1.
        'radial_rule_at_active_scale_rejected': Q(17)>Q(11,10)**4,
        # Omitting the height sends a nonterminal to its nearest terminal.
        'omit_height_rejected': Q(0)<(1-e)*Q(1),
        # Source upper factor alone ignores the global contraction budget.
        'ignore_common_lower_scale_rejected':
            (1+2*e)/(1-e)**2 > (1+2*e)/(1-e),
    }
    assert all(controls.values())
    print(json.dumps({'status':'PASS_EXACT_FINITE_NONPROOF',
                      'assertions':count,'bins_per_ordered_pair_at_kappa_quarter':M,
                      'extreme_scale_exponents':[-1000,0,1000],
                      'negative_controls':controls},sort_keys=True))

if __name__=='__main__':
    main()
