import math,json,pathlib
L=pathlib.Path(__file__).resolve().parent
out={'status':'finite screening only; no proof or novelty claim','checks':[]}
for k in range(101):
 s=2*k+1
 assert (s*s-1)*(s+3)*(5*s+17)*24==384*k*(k+1)*(k+2)*(5*k+11)
out['checks'].append({'id':332933,'executed':'integer cross-multiplication for s=2k+1, k=0..100','result':'matches source Theorem 3.10; finite evidence plus elementary symbolic substitution, not a partition proof audit'})
D=24009857226825282345490;N=24548583881;a=4030160489;M=977608342706
assert (D-a*a)%N==0
out['checks'].append({'id':332055,'executed':'exact integer comparison from source Theorem 4','bound':(D-a*a)//N,'M':M,'positive_gap':M-(D-a*a)//N,'limitation':'norm-minimality, squarefreeness and indecomposability not independently replayed'})
vals=[]
for x in [0,.2,.5,5]:
 a=27.23;b=.08;A=2.3-34;be=b*180/math.pi;P=1/(1+a*math.exp(-b*(180/math.pi*math.atan(x)-a)));F=-A*math.log(10)/10*be*P*(1-P)-2*x
 vals.append({'alpha':x,'derivative_sign_factor_float':F})
out['checks'].append({'id':332604,'executed':'binary64 derivative-sign factor at four points, High-rise Urban parameters and degrees as Eq.15','values':vals,'limitation':'not rigorous interval signs; Eq.12 omits degree conversion shown in Eq.15; source fidelity and closest successors unresolved; no credit for convention repair'})
(L/'bounded-checks.json').write_text(json.dumps(out,indent=2)+'\n');print(json.dumps(out,indent=2))
