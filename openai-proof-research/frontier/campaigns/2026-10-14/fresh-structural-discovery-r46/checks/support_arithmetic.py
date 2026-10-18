#!/usr/bin/env python3
"""Deterministic exact-integer checks; not a proof of the asymptotic theorem."""
import json,math
rows=[]
for r,den in [(2,4),(2,3),(3,4)]:
 for n in [16,32,64,128,256,512]:
  k=n//den;K=math.factorial(n)//math.factorial(n-k);B=math.comb(n,k);M=n**4*B**2*K
  # Squared bound for the sum of expected marginal total variations.
  assert B*B*K*n**4==M
  num=(2*M)**r;div=math.factorial(n)
  rows.append({'n':n,'r':r,'k':k,'M_bits':M.bit_length(),'support_bound_below_full_group':num<div,'log_support_ratio_approx':round(math.log(num)-math.log(div),6)})
print(json.dumps({'status':'PASS','protocol':'No randomness; exact factorial/integer comparison, logs only for display. M=n^4 binom(n,k)^2 (n)_k. These finite cases do not prove universal asymptotics.','rows':rows},indent=2))
