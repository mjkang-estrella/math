#!/usr/bin/env python3
# Copyright 2026 Myeongjin Kang. MIT.
"""Finite algebra controls only; no maximal-operator estimate is proved."""
from fractions import Fraction as F
import json

def main():
 lengths=[F(1,2**k) for k in range(8)]
 thresholds=[F(0),F(1,512),F(1,128),F(1,64),F(1,10),F(1,2),F(1),F(2)]
 cases=0
 for eps in thresholds:
  for gap in thresholds:
   for w in [F(1,16),F(1,4),F(1)]:
    chosen=[j for j,L in enumerate(lengths) if eps<L and gap<=w/L]
    assert not chosen or chosen==list(range(min(chosen),max(chosen)+1))
    cases+=1
 # Arbitrary scale masks are NOT the interval-selector lemma.
 assert [0,2]!=list(range(3))
 # Four-point analogue: P averages constants, M keeps two points.
 h=[F(1)]*4;mh=[F(1),F(1),F(0),F(0)];pmh=[sum(mh)/4]*4
 comm=[a-b for a,b in zip(pmh,mh)]
 assert sum(x*x for x in comm)==sum(x*x for x in h)/4
 # Rational interval and Taylor factor used in the continuous proof.
 assert F(1,4)<=F(11,20)<1
 assert 1-F(11,20)**2/6>F(1,2)
 assert F(1,2)*F(1,4)==F(1,8)
 print(json.dumps(dict(status='PASS_SCOPED_FINITE_CONTROLS',interval_cases=cases,arbitrary_noninterval_mask_rejected=True,mean_projection_commutator_squared_ratio='1/4',continuous_lower_bound_product='1/8',full_maximal_theorem_proved=False),indent=2))
if __name__=='__main__':main()
