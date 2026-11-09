from pathlib import Path
import sys,json,hashlib,itertools,time,resource
D=Path(sys.argv[1]).resolve();P=D/'evidence';start=time.monotonic()
def load(p):return json.loads(p.read_text())
def sha(b):return hashlib.sha256(b).hexdigest()
def plane(q):
 pts=[(1,a,b) for a in range(q) for b in range(q)]+[(0,1,a) for a in range(q)]+[(0,0,1)]
 def mul(a,b):
  if q!=4:return a*b%q
  v=0
  for _ in range(2):
   if b&1:v^=a
   b>>=1;a<<=1
   if a&4:a^=7
  return v
 def dot(a,b):
  v=[mul(x,y) for x,y in zip(a,b)]
  return v[0]^v[1]^v[2] if q==4 else sum(v)%q
 ls=[[i for i,x in enumerate(pts) if dot(x,u)==0] for u in pts];n=len(pts)
 assert n==q*q+q+1 and all(len(l)==q+1 for l in ls)
 assert all(sum(p in l for l in ls)==q+1 for p in range(n))
 assert all(sum(a in l and b in l for l in ls)==1 for a in range(n) for b in range(a))
 assert all(len(set(a)&set(b))==1 for i,a in enumerate(ls) for b in ls[:i])
 return pts,ls
controls=[]
for q,r,mask in [(4,4,1299211),(5,4,70588740),(5,5,241579737),(7,4,6831815575732480),(7,5,19422875086709251)]:
 pts,ls=plane(q);n=len(pts);full=(1<<n)-1;lm=[sum(1<<p for p in l) for l in ls]
 def step(a):
  b=a
  for l in lm:
   if (a&l).bit_count()>=r:b|=l
  return b
 def close(a):
  h=[a]
  while step(a)!=a:a=step(a);h.append(a)
  return h
 h=close(mask);deletions={str(i):close(mask^(1<<i))[-1] for i in range(n) if mask>>i&1}
 assert h[-1]==full and all(v!=full for v in deletions.values())
 controls.append(dict(q=q,r=r,mask=mask,size=mask.bit_count(),time=len(h)-1,round_sizes=[a.bit_count() for a in h],rounds=h,deletion_closures=deletions,minimal=True))
assert [x['time'] for x in controls]==[2,2,3,2,2]
assert [{k:v for k,v in c.items() if k in ['q','r','mask','rounds','deletion_closures']} for c in controls[:3]]==load(P/'percolation-review-r1/controls.json')[:3]
pts,ls=plane(5);clauses=[];families={}
def bits(n):return [[bool((k>>i)&1) for i in range(n)] for k in range(1<<n)]
def gate(vs,test):
 for bs in bits(len(vs)):
  if not test(bs):clauses.append([-v if b else v for v,b in zip(vs,bs)])
def family(name,fn):
 n=len(clauses);fn();families[name]=len(clauses)-n
def activation(offset,out):
 for l,line in enumerate(ls):gate([out+l]+[offset+p for p in line],lambda b:b[0]==(sum(b[1:])>=5))
family('activation_A',lambda:activation(1,63));family('activation_X',lambda:activation(32,94))
def spreads():
 for p in range(31):gate([32+p,1+p]+[63+l for l,line in enumerate(ls) if p in line],lambda b:b[0]==any(b[1:]))
family('spread',spreads)
family('final',lambda:[gate([32+p]+[94+l for l,line in enumerate(ls) if p in line],any) for p in range(31)])
family('closed',lambda:[gate([125+31*v+p for p in line],lambda b:sum(b)!=5) for v in range(31) for line in ls])
family('not_full',lambda:clauses.append([-32-p for p in range(31)]))
family('omit',lambda:[clauses.append([-1-v,-125-31*v-v]) for v in range(31)])
family('contain',lambda:[clauses.append([-1-v,-1-p,125+31*v+p]) for v in range(31) for p in range(31) if p!=v])
family('units',lambda:clauses.extend([[1],[26],[31]]))
b=(f'p cnf 1085 {len(clauses)}\n'+''.join(' '.join(map(str,c))+' 0\n' for c in clauses)).encode()
assert b==(D/'certificates/normalized.cnf').read_bytes();(D/'recomputed.cnf').write_bytes(b)
j=load(D/'certificates/normalized-trimmed.json');steps=j['steps'];db={i+1:set(c) for i,c in enumerate(clauses)};hint_uses=0;lit_uses=0
for cid,c,hints in steps:
 assert cid not in db;false=set(c);assert not any(-x in false for x in false)
 conflict=False
 for hint in hints:
  assert hint>0 and hint in db
  remaining=db[hint]-false
  if not remaining:conflict=True;break
  assert len(remaining)==1
  forced=next(iter(remaining));false.add(-forced)
 assert conflict;db[cid]=set(c);hint_uses+=len(hints);lit_uses+=len(c)
assert not steps[-1][1];assert j['inputs']==len(clauses)
mt=load(P/'percolation-formal-r8/module-times.json');total=round(sum(x['total_seconds'] for x in mt),2)
order=(P/'percolation-formal-r8/module-order.txt').read_text().splitlines()
assert len(mt)==len(order)==830
coll=[x for x in order if x.startswith(('CollF','CollG','CollH'))];assert len(coll)==86
result=dict(status='PASS',geometry=dict(points=len(pts),lines=len(ls),degree=6,point_pairs=31*30//2,line_pairs=31*30//2),controls=controls,cnf=dict(variables=4*31+31*31,clauses=len(clauses),base=len(clauses)-3,families=families,sha256=sha(b),byte_exact=True),certificate=dict(additions=len(steps),hint_uses=hint_uses,literal_occurrences=lit_uses,used_inputs=len(j['used_inputs']),last_id=steps[-1][0],empty_final=True,rup_recheck=True,bytes=(D/'certificates/normalized-trimmed.json').stat().st_size),formal_record=dict(modules=len(order),collineations=len(coll),developer_replay_seconds=total,compiler_seconds=round(sum(x['build_seconds'] for x in mt),2),checker_seconds=round(sum(x['check_seconds'] for x in mt),2),peak_rss_kib=max(max(x['build_rss_kib'],x['check_rss_kib']) for x in mt)),elapsed_seconds=time.monotonic()-start,peak_rss_kib=resource.getrusage(resource.RUSAGE_SELF).ru_maxrss)
(D/'recomputation.json').write_text(json.dumps(result,indent=2)+'\n');print(json.dumps({k:v for k,v in result.items() if k!='controls'},indent=2))
