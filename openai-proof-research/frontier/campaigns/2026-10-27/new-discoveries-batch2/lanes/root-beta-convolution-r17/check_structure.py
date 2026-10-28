from pathlib import Path
import json
import sympy as s
import mpmath as mp

p=Path(__file__).resolve().parent
a,al,be,k,i=s.symbols('a alpha beta k i',positive=True)
h=lambda t:(t+1)*(t+2)/2
summand=s.expand(h(a+al+i)*h(a+be+k-i)-h(a+i)*h(a+al+be+k-i))
P=s.factor(s.summation(summand,(i,0,k))/(al*be*(k+1)))
assert all(c>0 for c in s.Poly(s.expand(P),a,al,be,k).coeffs())
bracket=2*a*a+2*a*(al+be+k+3)+al*be+(al+be)*(k+3)+2*k+5
assert s.expand(P-bracket/4)==0
av,alv,bev=s.Rational(1,100),s.Rational(1,10),s.Rational(1,10)
hbad=lambda t:t*t
bad=s.factor(sum(hbad(av+alv+j)*hbad(av+bev+1-j)-hbad(av+j)*hbad(av+alv+bev+1-j) for j in range(2)))
assert bad==s.Rational(-3829,250000)
mp.mp.dps=170
w=json.loads((p/'screen.json').read_text())['worst']
b,a0,aa,bb=[mp.mpf(w[t]) for t in ['b','a','alpha','beta']];kk=w['k']
hh=lambda t:mp.gamma(t+b)/mp.gamma(t+1)/mp.gamma(b)
L=mp.fsum(hh(a0+aa+j)*hh(a0+bb+kk-j) for j in range(kk+1))
R=mp.fsum(hh(a0+j)*hh(a0+aa+bb+kk-j) for j in range(kk+1))
gap=(L-R)/(L+R);assert gap>0
out={'credit':0,'b3_normalized_psi_over_alpha_beta_kplus1':str(s.expand(P)),
     'b3_symbolic_positive_formula':str(bracket/4),'b3_exact_identity':'PASS',
     'generic_logconcavity_counterexample':{'h':'t^2','a':'1/100','alpha':'1/10','beta':'1/10','k':1,'psi':str(bad)},
     'smallest_gap_recheck':{'precision_dps':170,'method':'Direct Gamma products and summation, rather than scaled logGamma','parameters':'Reconstructed from saved35-digit parameters, not falsely described as exact original random reals','relative_gap':mp.nstr(gap,75)},
     'scope':'Uncounted partial b=3 and ruled-out generic route; no full b>2 result.'}
(p/'exact-structure.json').write_text(json.dumps(out,indent=2)+'\n')
print(json.dumps({'b3_identity':'PASS','generic_route':'REFUTED','tiny_gap_recheck':mp.nstr(gap,30),'credit':0}))
