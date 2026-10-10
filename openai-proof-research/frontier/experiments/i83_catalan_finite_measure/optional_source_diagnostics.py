"""Floating source-transcription diagnostics only; NOT analytic proof or asserted repairs."""
import math,json
x=-1/32;w=1+16*x
s=t=1.
for n in range(1,100):t*=((n-.5)/n)**2*w;s+=t
A=C=math.sqrt(w)*s
s=t=1.
for n in range(1,100):t*=n*n/(n+.5)**2*w;s+=t
D=-w/4*s
b0,b1=0.,1.;B=x
for n in range(2,100):
 b2=((16 if n==2 else 0)-(32*(n-1)**2-4)*b1-256*(n-2)**2*b0)/n**2
 B+=b2*x**n;b0,b1=b1,b2
G=.9159655941772190150546035149
print(json.dumps({'status':'UNCERTIFIED floating diagnostic; original printed formula retained; no correction used as premise','x':x,'terms':100,'A':A,'B':B,'C':C,'D':D,'printed_ICM_rhs_minus_lhs':B-G*A/2-math.pi**2*C/16-D,'opposite_G_sign_residual':B+G*A/2-math.pi**2*C/16-D,'first_optional_attempt':{'command':'import mpmath as m','exit_code':1,'stderr':"ModuleNotFoundError: No module named 'mpmath'"},'supplementary_recursion_normalization':'2002 arXiv Theorem 3 prints factor (-1)^n/4; Eskandari J0=8G and u0=8. Do not mix the normalizations. No recurrence-integral claim from that companion is used.'},indent=2,sort_keys=True))
