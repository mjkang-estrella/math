from pathlib import Path
import json,itertools as it
from fractions import Fraction as F
D=Path(__file__).resolve().parents[1]
types=[(0,0),(0,1),(0,2),(1,1),(1,2),(2,2)]
halves=[]
for ks in types:
 n0=ks.count(0);n1=ks.count(1);n2=ks.count(2)
 # (size, count, total weighted numerator); W=7*layer1+9*layer2
 halves.append([(sum(max(1,k) for k in ks),2**n1,int((7*F(2*n0+n1,2)+9*F(n1+4*n2,2))*2**n1)),(1+sum(ks),1,9*sum(ks))])
table=[]
for i,a in enumerate(halves):
 row=[]
 for j,b in enumerate(halves):
  choices=[]
  for x,y in [(0,0),(0,1),(1,0)]:
   s,c,w=a[x];t,d,z=b[y];choices.append((s+t,c*d,w*d+z*c))
  mx=max(s for s,c,w in choices);den=sum(c for s,c,w in choices if s==mx);num=sum(w for s,c,w in choices if s==mx);row.append(str(F(num,den)))
 table.append(row)
x=json.loads((D/'outputs/edge-certificate.json').read_text());x['half_types']=types;x['half_states']=halves;x['weighted_matrix']=table
x['all_tree_expected_weight_at_least_27']=all(F(z)>=27 for r in table for z in r)
(D/'outputs/edge-analytic-table.json').write_text(json.dumps(x,indent=2)+'\n')
print('halfstates',halves,'matrix',table,'positive_alphaP',F(134,135)+F(1,2500))
