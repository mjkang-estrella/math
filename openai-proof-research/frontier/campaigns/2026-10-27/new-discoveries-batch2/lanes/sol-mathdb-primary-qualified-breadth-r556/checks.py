import pathlib,json,itertools,math
from fractions import Fraction as F
O=pathlib.Path(__file__).resolve().parent
patterns={};normalized={};count=0
# Exhaustive only for explicitly bounded amounts, not a canonical-currency oracle.
for k in range(1,6):
 for cs in itertools.combinations(range(2,17),k):
  a=(1,)+cs;pat='+';prefix=[1]
  for c in cs:
   prefix.append(c);dp=[0]+[100]*32
   for n in range(1,33):dp[n]=1+min(dp[n-d] for d in prefix if d<=n)
   good=True
   for n in range(33):
    rem=n;g=0
    for d in reversed(prefix):q,rem=divmod(rem,d);g+=q
    if g!=dp[n]:good=False;break
   pat+='+' if good else '-'
  patterns.setdefault(pat,a)
  if cs[0]==2:normalized.setdefault(pat,a)
  count+=1
missing={p:a for p,a in patterns.items() if p not in normalized}
# Exact all roots for nondegenerate c1=c2=1 tree, 6 transitions only.
states={(F(1),F(1),F(1))};layers=[];values={F(1)}
for depth in range(1,7):
 ns=set()
 for a,b,c in states:
  A=a*a;B=-(4*c*b*a-b**3);C=c**3*a+c*c*b*b;disc=B*B-4*A*C
  assert disc>=0
  x=math.isqrt(disc.numerator);y=math.isqrt(disc.denominator)
  assert x*x==disc.numerator and y*y==disc.denominator
  for sign in [-1,1]:
   d=(-B+sign*F(x,y))/(2*A);assert A*d*d+B*d+C==0;ns.add((b,c,d));values.add(d)
 states=ns;layers.append({'depth':depth,'distinct_states':len(states)})
r={'coins':{'currencies':count,'largest_coin_at_most':16,'coins_at_most':6,'amounts_checked':[0,32],'observed_patterns':len(patterns),'patterns_without_observed_first_coin_two':{p:list(a) for p,a in missing.items()},'limit':'Finite amount signatures only; neither all-amount orderliness nor all patterns established.'},'somos':{'parameters':[1,1],'initial':[1,1,1],'layers':layers,'distinct_values':len(values),'nonintegral_values':[str(v) for v in sorted(values) if v.denominator!=1],'limit':'Exact rationality and recurrence residuals in finite tree only; no general product factorization or full-scope result.'}}
(O/'calculation-results.json').write_text(json.dumps(r,indent=2)+'\n');print(json.dumps(r,indent=2))
