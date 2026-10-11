import sys,json
from pathlib import Path
from collections import Counter
sys.path.insert(0,str(Path(__file__).resolve().parent))
from toolkit import *
p=Path(__file__).parent;data=json.loads((p/'audit-attempt-02.json').read_text());r=[]
for i in data['first_test_order']+[i for i in range(636) if i not in data['first_test_order']]:
 z=data['rows'][i];es=list(map(tuple,z['parent_edges']));u,v,x,y,*_=z['labels']
 if edge(u,x) not in es or edge(v,y) not in es or z['l']==0:continue
 cs={k:[frozenset(map(tuple,c)) for c in cc] for k,cc in z['classes'].items()};L=differences(cs['N10']+cs['N01']+cs['N11'],es);V=differences(cs['N00'],es);rr=sub(vec(cs['N00'][0],es),vec(cs['N10'][0],es));s=[int(e in [edge(u,v),edge(x,y)])-int(e in [edge(u,x),edge(v,y)]) for e in es]
 if rank_integer(L+V+[rr])==rank_integer(L+V):coef=None
 else:
  w=next(w for w in nullspace(L+V,len(es)) if dot(w,rr));coef=Fraction(dot(w,s),dot(w,rr));assert rank_integer(L+V+[[coef.denominator*a-coef.numerator*b for a,b in zip(s,rr)]])==rank_integer(L+V)
 r.append({'i':i,'triple':[z['l'],z['t'],z['eta']],'coefficient':str(coef)})
print(json.dumps({'rows':r,'counts':dict(Counter(z['coefficient'] for z in r))},sort_keys=True,indent=2))
