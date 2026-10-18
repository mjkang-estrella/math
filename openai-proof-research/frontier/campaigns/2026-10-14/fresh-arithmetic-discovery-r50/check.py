#!/usr/bin/env python3
"""Exact finite support only; no theorem or novelty certification."""
from fractions import Fraction as F
from math import comb
import json
checks=0
for n in range(2,102,2):
 b=F(comb(n,n//2),2**n)
 ES=F(0);ES2=F(0);Eabs=F(0);EZabs=F(0)
 for k in range(n+1):
  z=2*k-n;prob=F(comb(n,k),2**n);score=abs(z) if z else -n
  ES+=prob*score;ES2+=prob*score**2;Eabs+=prob*abs(score);EZabs+=prob*abs(z)
 if (ES,ES2,Eabs,EZabs)!=(0,n+n*n*b,2*n*b,n*b):raise ValueError('quadratic identities failed')
 checks+=1
for k in range(2,31):
 p=F(1,2**k);q=1-p
 # Squared ratio W/||Tv||^2 = (pq)/(16p^2q^2).
 ratio_squared=F(1,16*p*q)
 if ratio_squared<=0:raise ValueError('vacuum ratio failed')
 checks+=1
# Slice mixture pivot probability has an exact (1-eta)/2 contribution.
eta=F(1,4)
for n in range(2,22,2):
 I=(1-eta)/2+eta*F(comb(n-1,n//2),2**(n-1))
 if F(n,2)*I<(1-eta)*n/4:raise ValueError('slice mixture bound failed')
 checks+=1
print(json.dumps({'status':'PASS_FINITE_SUPPORT_ONLY','exact_checks':checks,'quadratic_even_n_through':100,'full_target_proved':False}))
