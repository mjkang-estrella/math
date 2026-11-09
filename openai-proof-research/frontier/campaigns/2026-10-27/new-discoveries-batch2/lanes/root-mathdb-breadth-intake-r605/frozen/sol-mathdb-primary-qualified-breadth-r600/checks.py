import json,pathlib
from fractions import Fraction as F
D=pathlib.Path(__file__).resolve().parent
A=[[0,0],[1,0]];H=[[1],[0]];C=[[1,0],[0,1]];L0=[[1,0],[0,0]];L1=[[0,1],[0,0]]
def mul(a,b):return [[sum(x*y for x,y in zip(r,c)) for c in zip(*b)] for r in a]
AH=mul(A,H);S1=[AH[i]+H[i] for i in range(2)]
assert mul(L0,H)==H and mul(L1,S1)==[[1,0],[0,0]]
# Binary line, L=3 K=1: distinct channel columns have an affine dependence.
W=[[F(0),F(1,2),F(1)],[F(1),F(1,2),F(0)]]
assert mul(W,[[1],[-2],[1]])==[[0],[0]]
checks={'delay':{'executed':True,'A':A,'C':C,'H':H,'L_r0':L0,'L_r1':L1,'L0_CH':mul(L0,H),'L1_CAH_CH':mul(L1,S1),'scope':'two distinct delay gains satisfy source Eq3.1; source Theorem3.1 directly supplies the rank criterion, so routine source adaptation objection is decisive; no discovery proposal'},'tensor':{'executed':True,'L':3,'output_alphabet':2,'K':1,'columns':[['0','1'],['1/2','1/2'],['1','0']],'kernel':[1,-2,1],'scope':'one illustration only; general binary-line degree<=K dimension argument is classical and source already uses Bernstein interpolation; corpus statement also differs from primary v5'}}
(D/'bounded-checks.json').write_text(json.dumps(checks,indent=2)+'\n')
ids={r['mathdb_id'] for r in json.loads((D/'literal-records.json').read_text())}
files=[D.parent/'root-mathdb-accepted-exclusions-r304/accepted-exclusions.json',D.parent/'root-mathdb-accepted-exclusions-r304/historical-dispositions.json']
hits=[]
def visit(x):
 if isinstance(x,dict):
  for k,v in x.items():
   if k in ['mathdb_id','related_mathdb_id'] and v in ids:hits.append(x)
   visit(v)
 elif isinstance(x,list):
  for a in x:visit(a)
for p in files:visit(json.loads(p.read_text()))
(D/'prior-context-check.json').write_text(json.dumps({'assigned_id_hits':hits,'limit':'Exact scalar ID check only; no family/novelty clearance. r363 Cayley decision and r599 adjudications read and preserved.'},indent=2)+'\n')
print(json.dumps(checks,indent=2));print('r304 exact scalar matches',len(hits))
