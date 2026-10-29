import json,hashlib,pathlib
from html.parser import HTMLParser
class Text(HTMLParser):
 def __init__(self):super().__init__();self.parts=[]
 def handle_data(self,d):self.parts.append(d)
 def result(self):return " ".join(self.parts)
P=pathlib.Path(__file__).resolve().parent;B=P.parent.parent
for n in ['acyclic','acyclic-abs']:
 s=Text();s.feed((P/"sources"/f"{n}.html").read_text());(P/"sources"/f"{n}.txt").write_text(s.result())
rows={}
for name in ['ledger.json','prior-campaign-context.json']:
 p=B/name;d=json.loads(p.read_text());rows[name]={'sha256':hashlib.sha256(p.read_bytes()).hexdigest(),'accepted':[{k:x[k] for k in ['number','title','scope','source_target'] if k in x} for x in d['accepted']]}
(P/'context-screen.json').write_text(json.dumps(rows,indent=2)+'\n')
# 4-state exact transfer table certificate, every proper row has a unique color-normalization.
from itertools import product
rr=[r for r in product(range(3),repeat=4) if all(a!=b for a,b in zip(r,r[1:]))]
def norm(a):
 d={};return tuple(d.setdefault(c,len(d)) for c in a)
rep=sorted(set(map(norm,rr)));M=[[sum(norm(s)==t and all(x!=y for x,y in zip(r,s)) for s in rr) for t in rep] for r in rep]
v=[1]*4;vec=[v]
for i in range(3):v=[sum(M[j][k]*v[k] for k in range(4)) for j in range(4)];vec.append(v)
assert 6*sum(v)==7812
(P/'transfer-certificate.json').write_text(json.dumps({'representatives':rep,'transition_matrix':M,'per_fixed_row_vectors':vec,'total':6*sum(v)},indent=2)+'\n')
print(json.dumps({'representatives':rep,'matrix':M,'vectors':vec,'total':6*sum(v)}))
