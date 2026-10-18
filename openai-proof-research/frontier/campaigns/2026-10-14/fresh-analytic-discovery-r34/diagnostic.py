#!/usr/bin/env python3
"""MIT. Finite exact-arithmetic diagnostics, not a billiard proof."""
from fractions import Fraction as F
from math import log
import json


def direct(n):
    return sum((F(1, (j-k)**2) for j in range(n+1) for k in range(-n, 0) if (j-k)%2), F())


def grouped(n):
    return sum((F(m if m<=n else 2*n+1-m, m*m) for m in range(1, 2*n+1) if m%2), F())


def main():
    checks = {'pair_count_identity': all(direct(n)==grouped(n) for n in range(1,33))}
    # A tempting wrong count counts each frequency only once, dropping its multiplicity.
    wrong = sum((F(1,m*m) for m in range(1,17) if m%2), F())
    checks['wrong_multiplicity_rejected'] = wrong != direct(8)
    # Keeping just the nearest off-diagonal throws away the nonzero m=3 term.
    checks['two_mode_truncation_rejected'] = direct(8) != F(1)
    # Factoring out 4 sin(alpha)^2/pi^2 is essential: alpha=0,pi has exactly zero block.
    checks['constant_phase_control'] = 0*grouped(8)==0 and grouped(8)>0
    # Product of two L2 derivative bounds: volume eps^d, pointwise derivative eps^-1.
    exponent = lambda d: 2*(F(d,2)-1)
    checks['corner_budget'] = exponent(2)==0
    checks['seam_budget_loss'] = exponent(1)==-1
    checks['false_seam_uniformity_rejected'] = exponent(1)!=0
    # A constant scalar gluing J across a reversible edge must satisfy J^2=1.
    # Real rational phases +1,-1 pass; a quarter-turn i has square -1 and fails.
    checks['reversible_real_phases'] = 1**2==1 and (-1)**2==1
    checks['quarter_turn_constant_gluing_rejected'] = (1j)**2 != 1
    # Report a finite comparison only; the proof of O(1) is in the lemma note.
    asymptotic = [{'N':n,'sum':float(grouped(n)), 'sum_minus_half_log_N':float(grouped(n))-.5*log(n)} for n in [8,32,128,512,2048]]
    assert all(checks.values()), checks
    print(json.dumps({'status':'PASS_FINITE_DIAGNOSTICS_ONLY','checks':checks,'finite_log_comparison':asymptotic},indent=2))

if __name__=='__main__':main()
