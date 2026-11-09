from pathlib import Path
from fractions import Fraction
from math import lcm,gcd
import json
from checks import certify
L=Path(__file__).resolve().parent
r=json.loads((L/'boundary-result.json').read_text());out=[]
for v in r['vertices']:
 x,y=map(Fraction,v['point']);a=lcm(x.denominator,y.denominator);t=(a,int(a*x),int(a*y));g=gcd(gcd(t[0],t[1]),t[2]);t=tuple(z//g for z in t)
 if t[0]>=12 and tuple(z%3 for z in t) in map(tuple,v['residues']):out.append(certify(t))
(L/'vertices-result.json').write_text(json.dumps(out,indent=2));print('eligible vertices',len(out),'full passing',[z['triple'] for z in out if z['bad'] is None])
