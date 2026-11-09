from pathlib import Path
from fractions import Fraction as Q
from itertools import permutations
import json,re,ast,signal,hashlib
signal.alarm(90)
OUT=Path(__file__).parent; OLD=OUT.parent/'hereditary-trace-fresh-r1'
def cyc(w):return min(w[i:]+w[:i] for i in range(len(w)))
def add(p,q,c=Q(1)):
 for m,a in q.items():
  p[m]=p.get(m,Q(0))+c*a
  if not p[m]:del p[m]
def mul(p,q):
 r={}
 for m,a in p.items():
  for n,b in q.items():add(r,{tuple(sorted(m+n)):a*b})
 return r
def F(bs):
 p={}
 for s in permutations(range(4)):
  seen=set();cs=[]
  for i in range(4):
   if i in seen:continue
   w=();j=i
   while j not in seen:seen.add(j);w+=bs[j];j=s[j]
   cs.append(cyc(w))
  add(p,{tuple(sorted(cs)):Q((-1)**(4-len(cs)))})
 return p
def parse(xs):return {tuple(tuple(map(int,w)) for w in x['traces']):Q(x['coefficient']) for x in xs}
def enc(p):return [{'traces':[''.join(map(str,w)) for w in m],'coefficient':str(c)} for m,c in sorted(p.items())]
def traceless(p):return {m:c for m,c in p.items() if all(len(w)>1 for w in m)}
def sub(p,pat):
 r={}
 for m,c in p.items():add(r,{tuple(sorted(cyc(tuple(pat[a-1] for a in w)) for w in m)):c})
 return r
D=json.loads((OLD/'trace-exact-polynomials.json').read_text());q=traceless(parse(D['q']));polar=parse(D['polarized_q'])
low=[traceless(parse(x)) for x in D['lower_identity_products']]
# Lower columns tracked by index; all arithmetic equality certificates re-expanded.
basis={}
def reduce(p,proof=None):
 p=dict(p);proof={} if proof is None else dict(proof)
 while p:
  m=min(p)
  if m not in basis:break
  v,c=basis[m];a=p[m];add(p,v,-a);add(proof,c,-a)
 return p,proof
for i,p in enumerate(low):
 r,c=reduce(p,{i:Q(1)})
 if r:
  m=min(r);a=r[m];basis[m]=({n:v/a for n,v in r.items()},{n:v/a for n,v in c.items()})
def normal(p):
 p=dict(p);r={}
 while p:
  m=min(p)
  if m in basis:add(p,basis[m][0],-p[m])
  else:r[m]=p.pop(m)
 return r
# Literal E expressions of degrees 2..5; degree6 cannot appear in degree7 after traceless specialization.
expr={1:'11',2:'22',3:'33',4:'12',5:'13',6:'23',7:'111',8:'222',9:'333',10:'112',11:'113',12:'221',13:'223',14:'331',15:'332',16:'123+132',17:'123-132',18:'1122-1212',19:'1133-1313',20:'2233-2323',21:'1123+1132-2*1213',22:'2213+2231-2*2123',23:'3312+3321-2*3132',24:'1123-1132',25:'2213-2231',26:'3312-3321',27:'11213-11312',28:'22123-22321',29:'33231-33132',30:'21213+11223-12312-11322',31:'31312+11332-13213-11233',32:'23231+33221-23123-33122',33:'11223+11322+12123+12132-2*11232-2*12213',34:'11332+11233+13132+13123-2*11323-2*13312',35:'22331+22133+23231+23213-2*22313-2*23321'}
E={};degrees={}
for i,s in expr.items():
 p={}
 for sign,k,w in re.findall(r'([+-]?)(?:(\d+)\*)?([123]+)',s):add(p,{(cyc(tuple(map(int,w))),):Q((-1 if sign=='-' else 1)*int(k or 1))})
 E[i]=p;w=next(iter(p))[0];degrees[i]=tuple(w.count(a) for a in (1,2,3))
target=(3,2,2);emons=[];epols=[]
def enum(rem,lo=1,mon=(),pol={():Q(1)}):
 if rem==(0,0,0):emons.append(mon);epols.append(pol);return
 for i in E:
  if i<lo:continue
  d=degrees[i]
  if all(x<=y for x,y in zip(d,rem)):enum(tuple(y-x for x,y in zip(d,rem)),i,mon+(i,),mul(pol,E[i]))
enum(target)
# CE columns extend low basis. If independent, this gives unambiguous finite elimination.
nlow=len(low); lowrank=len(basis)
for j,p in enumerate(epols):
 r,c=reduce(p,{nlow+j:Q(1)})
 assert r,('CE dependence',emons[j])
 m=min(r);a=r[m];basis[m]=({n:v/a for n,v in r.items()},{n:v/a for n,v in c.items()})
def ce(p):
 r,c=reduce(p)
 assert not r,('outside CE+lower',len(r))
 # p = -sum(c_i columns)
 co={i:-a for i,a in c.items()}
 check={}
 for i,a in co.items():add(check,(low+epols)[i],a)
 assert check==p
 return {emons[i-nlow]:a for i,a in co.items() if i>=nlow},co
def eenc(p):return [{'generators':list(m),'coefficient':str(c)} for m,c in sorted(p.items())]
qp,qcert=ce(q)
# Extract the literal thesis reduction, not an arbitrary retraction.
th=(OLD/'sources/hoge-thesis.txt').read_text(); segment=th[th.index('[[1, 2, 3], [4, 5], [6], [7]]   3055/864'):th.index('Dabei steht zum Beispiel')]
rows=re.findall(r'(\[\[(?:[0-9,\[\] ]+)\]\])\s*([−-]?\d+/\d+)',segment)
p0id={};thcert=[]
for bs,c in rows:
 bs=tuple(tuple(w) for w in ast.literal_eval(bs));c=Q(c.replace('−','-'));add(p0id,F(bs),c);thcert.append((bs,c))
top={m:c for m,c in p0id.items() if len(m)==1}
print('thesis tuples',len(rows),'top',enc(top),flush=True)
assert top=={((1,2,3,4,5,6,7),):Q(-1)} or top=={((1,2,3,4,5,6,7),):Q(1)}
a=next(iter(top.values()));p0={m:-c/a for m,c in p0id.items() if len(m)>1}
M=((1,1,1),(2,2),(3,),(3,))
reports=[]
for perm in [(1,2,3),(1,3,2)]:
 bs=tuple(tuple(perm[a-1] for a in w) for w in M);f=F(bs);r0=traceless({m:c for m,c in f.items() if len(m)>1});delta={}
 for m,c in f.items():
  if len(m)==1:add(r0,traceless(sub(p0,m[0])),c);add(delta,traceless(sub(polar,m[0])),c)
 rp,rc=ce(r0);dp,dc=ce(delta)
 ratio=lambda p:next(iter(p.values()))/qp[next(iter(p))] if p else Q(0)
 rr=ratio(rp);dr=ratio(dp)
 assert rp=={m:c*rr for m,c in qp.items() if c*rr}
 assert dp=={m:c*dr for m,c in qp.items() if c*dr}
 reports.append({'letter_permutation':perm,'P0_multiple_of_q':str(rr),'delta_multiple_of_q':str(dr),'annihilating_t':str(-rr/dr) if dr else None,'P0_CE':eenc(rp),'delta_CE':eenc(dp),'P0_elimination_certificate':{str(i):str(c) for i,c in rc.items()},'delta_elimination_certificate':{str(i):str(c) for i,c in dc.items()}})
print('CE monomials',len(emons),'low rank',lowrank,'q',eenc(qp),flush=True)
print('stabilizer audit',[(r['letter_permutation'],r['P0_multiple_of_q'],r['delta_multiple_of_q'],r['annihilating_t']) for r in reports],flush=True)
packet={'scope':'traceless specialization of literal CE, exact QQ polynomial expansions; not Lean checked','low_rank':lowrank,'CE_monomials':list(map(list,emons)),'E_formulas':expr,'q_CE':eenc(qp),'q_elimination_certificate':{str(i):str(c) for i,c in qcert.items()},'column_convention':'0..242 inherited lower_identity_products after deleting singleton traces; then CE_monomials expanded by E_formulas','thesis_tuple_count':len(rows),'thesis_top':enc(top),'stabilizer_audit':reports}
(OUT/'finite-elimination.json').write_text(json.dumps(packet,indent=2))
explicit={'P0_definition':'minus decomposable part divided by single-trace coefficient of the following fundamental combination','fundamental_combination':[{'blocks':[''.join(map(str,w)) for w in bs],'coefficient':str(c)} for bs,c in thcert],'fundamental_single_trace_coefficient':str(a),'Pstar':'P0 - (47/864) Q','Q':'polarized_q in the hash-bound sibling trace-exact-polynomials.json; full unnormalized polarization','P0_expanded':enc(p0),'Q_expanded':enc(polar)}
(OUT/'explicit-reduction.json').write_text(json.dumps(explicit,indent=2))
