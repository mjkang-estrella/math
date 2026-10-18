#!/usr/bin/env python3
# Original code: Myeongjin Kang, MIT. Arithmetic diagnostics, not a theorem proof.
from fractions import Fraction as Q
import json

def exponents(A=Q(99,100), b=Q(1,10000), w=Q(1,100000)):
    alpha=A-15*b; alpha0=A-9*b; eta=40-15*w; eta0=40-9*w
    return {
      'alpha':alpha, 'alpha0':alpha0, 'eta':eta, 'eta0':eta0,
      'coulomb_u':(1-A)/4-Q(5,2)*b,
      'coulomb_r':Q(2,100)/4-Q(5,2)*w,
      'negative_field_u':1-A-3*b,
      'negative_field_r':Q(2,100)-3*w,
      'potential_u':(1-A)/2-b/2,
      'potential_r':Q(2,100)/2-w/2,
      'observation_sandwich':Q(1,100)-4*w,
      'fine_sandwich':Q(2,10)-4*w,
      'dyadic_gain_u':7*alpha/2-3,
      'dyadic_gain_r':eta/2-3,
      'initial_lambda_decay_u':Q(7,3)*alpha0-1,
      'initial_lambda_decay_r':eta0/3-1,
    }

def closes(d):
    return all(v>0 for k,v in d.items()) and d['alpha']<1 and d['alpha0']<1

def main():
    d=exponents(); assert closes(d)
    assert d['coulomb_u']==Q(9,4000)
    assert d['dyadic_gain_u']==Q(1839,4000)
    # Each deliberately wrong parameter choice violates an actual necessary margin.
    mutations={
      'no_probability_margin_A_equals_1':exponents(A=Q(1)),
      'excessive_packet_exponent_b':exponents(b=Q(1,100)),
      'insufficient_bad_probability_A':exponents(A=Q(4,5)),
      'too_narrow_r_packet_w':exponents(w=Q(1,100)),
    }
    for name,v in mutations.items():assert not closes(v),name
    # Exact finite geometric sum. For positive g, inward dyadic scales are bounded
    # by the infinite geometric sum; g<=0 does not admit that uniform bound.
    # Here use rational integer g=1,2,3 as explicit code controls, not the real-power theorem.
    for g in (1,2,3):
      for J in (1,4,20):
        total=sum(Q(1,2)**(j*g) for j in range(J+1))
        assert total==(1-Q(1,2)**((J+1)*g))/(1-Q(1,2)**g)
        assert total<1/(1-Q(1,2)**g)
    assert sum(Q(1) for _ in range(21))>10
    # Newton angular-average elementary antiderivative (r,d positive) is
    # [(r+d)-abs(r-d)]/(2*r*d)=1/max(r,d); test nonsymmetric point shells.
    for r,d0 in ((Q(1),Q(3)),(Q(5),Q(2)),(Q(2),Q(2))):
      angular=((r+d0)-abs(r-d0))/(2*r*d0)
      assert angular==1/max(r,d0)
      if d0>=2*r:assert 1-r/d0>=Q(1,2)
    assert 1-Q(1,1)/Q(3,2)<Q(1,2) # wrong exterior threshold 1.5r fails
    print(json.dumps({'status':'PASS_ARITHMETIC_ONLY','exponents':{k:str(v) for k,v in d.items()},'negative_controls':{k:[n for n,vv in v.items() if vv<=0] for k,v in mutations.items()},'limits':'Finite rational arithmetic; no verification of source contracts, conditional analysis, PDE argument, or substantiality.'},indent=2))
if __name__=='__main__':main()
