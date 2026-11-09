"""Independent equality-only verifier. No ranks, no source-generation-script import.
This is exact Python arithmetic, NOT a Lean/kernel certificate.
"""
from pathlib import Path
from fractions import Fraction
from itertools import permutations
from collections import defaultdict
import json,signal
signal.alarm(60)
p=Path(__file__).parent;old=p.parent/'hereditary-trace-fresh-r1'
d=json.loads((old/'trace-exact-polynomials.json').read_text());el=json.loads((p/'finite-elimination.json').read_text());ex=json.loads((p/'explicit-reduction.json').read_text())
Q=Fraction
def canon(w):return min(w[i:]+w[:i] for i in range(len(w)))
def add(*polys):
 r=defaultdict(Q)
 for pol in polys:
  for k,v in pol.items():r[k]+=v
 return {k:v for k,v in r.items() if v}
def scale(c,pol):return {k:c*v for k,v in pol.items() if c*v}
def read(xs):return {tuple(tuple(map(int,w)) for w in t['traces']):Q(t['coefficient']) for t in xs}
def ft(blocks):
 r=[]
 for perm in permutations(range(4)):
  remaining=set(range(4));cycles=[]
  while remaining:
   start=min(remaining);j=start;w=()
   while j in remaining:remaining.remove(j);w+=blocks[j];j=perm[j]
   cycles.append(canon(w))
  r.append({tuple(sorted(cycles)):Q((-1)**(4-len(cycles)))})
 return add(*r)
def fundamental_certificate(xs):return add(*(scale(Q(x['coefficient']),ft(tuple(tuple(map(int,w)) for w in x['blocks']))) for x in xs))
def center(pol):return {m:c for m,c in pol.items() if all(len(w)>1 for w in m)}
def subst(pol,pat):return add(*({tuple(sorted(canon(tuple(pat[i-1] for i in w)) for w in m)):v} for m,v in pol.items()))
def multiply(a,b):return add(*({tuple(sorted(m+n)):c*e} for m,c in a.items() for n,e in b.items()))
q=read(d['q']);assert fundamental_certificate(d['q_fundamental_certificate'])==q
polar={}
for mon,c in q.items():
 flat=sum((list(w) for w in mon),[])
 locs=[[i for i,a in enumerate(flat) if a==k] for k in (1,2,3)]
 for a in permutations((1,2,3)):
  for b in permutations((4,5)):
   for cc in permutations((6,7)):
    lab=flat.copy()
    for pos,labels in zip(locs,(a,b,cc)):
     for i,v in zip(pos,labels):lab[i]=v
    offset=0;words=[]
    for w in mon:words.append(canon(tuple(lab[offset:offset+len(w)])));offset+=len(w)
    polar=add(polar,{tuple(sorted(words)):c})
assert polar==read(ex['Q_expanded'])==read(d['polarized_q'])
assert all(sorted(sum((list(w) for w in m),[]))==list(range(1,8)) and max(map(len,m))<=6 for m in polar)
id0=fundamental_certificate(ex['fundamental_combination']);top={m:c for m,c in id0.items() if len(m)==1}
assert top=={((1,2,3,4,5,6,7),):Q(-1)}
p0=read(ex['P0_expanded']);assert add(p0,scale(-1,id0),{((1,2,3,4,5,6,7),):Q(-1)})=={}
assert all(sorted(sum((list(w) for w in m),[]))==list(range(1,8)) and max(map(len,m))<=6 for m in p0)
# Independent expression parser via splitting signs; CE polynomials checked as formal trace expansions.
E={}
for k,s in el['E_formulas'].items():
 r={}
 for term in s.replace('-','+-').split('+'):
  if not term:continue
  if '*' in term:a,w=term.split('*');a=Q(a)
  else:a,w=(Q(-1),term[1:]) if term.startswith('-') else (Q(1),term)
  r=add(r,{(canon(tuple(map(int,w))),):a})
 E[int(k)]=r
def expand(mon):
 r={():Q(1)}
 for i in mon:r=multiply(r,E[i])
 return r
cols=[center(read(x)) for x in d['lower_identity_products']]+[expand(m) for m in el['CE_monomials']]
def verify(pol,ce,cert):
 rhs=add(*(scale(Q(c),cols[int(i)]) for i,c in cert.items()));assert pol==rhs
 rhsce=add(*(scale(Q(x['coefficient']),expand(x['generators'])) for x in ce))
 lowerpart=add(*(scale(Q(c),cols[int(i)]) for i,c in cert.items() if int(i)<len(d['lower_identity_products'])))
 assert pol==add(rhsce,lowerpart)
verify(center(q),el['q_CE'],el['q_elimination_certificate'])
for r in el['stabilizer_audit']:
 perm=r['letter_permutation'];bs=tuple(tuple(perm[i-1] for i in w) for w in ((1,1,1),(2,2),(3,),(3,)))
 f=ft(bs);short={m:c for m,c in f.items() if len(m)>1};r0=dict(short);delta={}
 for m,c in f.items():
  if len(m)==1:r0=add(r0,scale(c,subst(p0,m[0])));delta=add(delta,scale(c,subst(polar,m[0])))
 verify(center(r0),r['P0_CE'],r['P0_elimination_certificate']);verify(center(delta),r['delta_CE'],r['delta_elimination_certificate'])
 def cepoly(xs):return {tuple(x['generators']):Q(x['coefficient']) for x in xs}
 assert add(cepoly(r['P0_CE']),scale(Q(-47,864),cepoly(r['delta_CE'])))=={}
qce={tuple(x['generators']):Q(x['coefficient']) for x in el['q_CE']};assert qce[(1,35)]==Q(1,6)
value=sum(c*(6 if 1 in m else 1) for m,c in qce.items() if set(m)<={1,35});assert value==1
print(json.dumps({'status':'PASS','arithmetic':'Fraction exact QQ, equality certificates only','P0_fundamental_columns':len(ex['fundamental_combination']),'Q_terms':len(polar),'q_CE_terms':len(qce),'CE_separating_evaluation':{'T1':6,'T35':1,'other_T':0,'q_value':str(value)},'stabilizer_permutations_checked':2,'parameter':'-47/864','Lean_checked':False},indent=2))
lo=json.loads((p/'low-injectivity.json').read_text())
def matrix_product(a,b):return [[sum(a[i][k]*b[k][j] for k in range(3)) for j in range(3)] for i in range(3)]
def trace_word(mats,w):
 a=[[int(i==j) for j in range(3)] for i in range(3)]
 for letter in w:a=matrix_product(a,mats[int(letter)-1])
 return sum(a[i][i] for i in range(3))
def evalues(mats):
 assert all(sum(a[i][i] for i in range(3))==0 for a in mats)
 r={}
 for k,s in lo['E_formulas'].items():
  val=0
  for term in s.replace('-','+-').split('+'):
   if not term:continue
   if '*' in term:a,w=term.split('*');a=int(a)
   else:a,w=(-1,term[1:]) if term.startswith('-') else (1,term)
   val+=a*trace_word(mats,w)
  r[int(k)]=val
 return r
vs=[evalues(a) for a in lo['samples']]
covered=set()
for rec in lo['components']:
 covered.add(tuple(rec['multidegree']));ms=rec['CE_monomials'];computed=[]
 for si in rec['sample_indices']:
  row=[]
  for mon in ms:
   v=1
   for i in mon:v*=vs[si][i]
   row.append(v)
  computed.append(row)
 assert computed==rec['evaluation_matrix']
 inv=[[Q(x) for x in row] for row in rec['inverse']];n=len(ms)
 assert len(computed)==n
 for i in range(n):
  for j in range(n):assert sum(Q(computed[i][k])*inv[k][j] for k in range(n))==int(i==j)
# Check monomial lists are complete by an independent brute force of partitions of weight<=6.
from itertools import combinations_with_replacement
weights={}
for k,s in lo['E_formulas'].items():
 w=s.replace('-','+').split('+')[0].split('*')[-1];weights[int(k)]=tuple(w.count(str(i)) for i in (1,2,3))
allmons={}
for length in range(1,4):
 for m in combinations_with_replacement(sorted(weights),length):
  degree=tuple(sum(weights[k][i] for k in m) for i in range(3))
  if sum(degree)<=6:allmons.setdefault(degree,set()).add(m)
assert covered==set(allmons)
for rec in lo['components']:assert set(map(tuple,rec['CE_monomials']))==allmons[tuple(rec['multidegree'])]
print(json.dumps({'low_degree_injectivity':'PASS exact evaluated matrices times inverses equal identity','components':len(covered),'max_dimension':lo['max_dimension'],'scope':'all centered CE monomials of total weight 1..6; generator degrees>=2; scalar trace variables extend by polynomial tensor product','Lean_checked':False},indent=2))
