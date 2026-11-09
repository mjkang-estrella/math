import os,resource,signal,re,json,itertools,time,hashlib
from pathlib import Path
resource.setrlimit(resource.RLIMIT_AS,(512*1024**2,)*2);resource.setrlimit(resource.RLIMIT_CPU,(210,210));signal.alarm(230)
os.environ.update(OPENBLAS_NUM_THREADS='1',OMP_NUM_THREADS='1');F=Path('extracted/formal');start=time.monotonic()
# Independent parser for the frozen literal expression language, not Lean evaluation.
class Parser:
 def __init__(self,s):self.t=re.findall(r'i\.val|[A-Za-z_][A-Za-z_0-9]*|\d+|[^\s]',s);self.j=0
 def pop(self,t=None):
  x=self.t[self.j];self.j+=1
  if t is not None:assert x==t,(x,t)
  return x
 def expr(self,level=0):
  x=self.pop()
  if x=='if':
   c=self.expr();self.pop('then');a=self.expr();self.pop('else');b=self.expr();v=('if',c,a,b)
  elif x=='(':
   v=self.expr()
   if self.t[self.j]==',':self.pop();v=('pair',v,self.expr())
   self.pop(')')
  elif x=='{':
   a=[]
   while self.t[self.j]!='}':
    a.append(self.expr())
    if self.t[self.j]==',':self.pop()
    else:break
   self.pop('}');v=('set',a)
  elif x=='-':v=('neg',self.expr(30))
  elif x.isdecimal():v=int(x)
  elif x.startswith('rows'):v=('call',x,self.expr(30))
  else:assert x in ['i','i.val','m'],x;v=('var',x)
  while self.j<len(self.t):
   op=self.t[self.j];p={'<':5,'+':10,'-':10,'/':20,'%':20}.get(op,-1)
   if p<level:break
   self.pop();v=(op,v,self.expr(p+1))
  return v
 def parse(self):
  v=self.expr();assert self.j==len(self.t),(self.t[self.j:]);return v
def ev(a,x,funcs):
 if isinstance(a,int):return a
 op=a[0]
 if op=='var':return x[a[1]] if isinstance(x,dict) else x
 if op=='if':return ev(a[2] if ev(a[1],x,funcs) else a[3],x,funcs)
 if op=='neg':return -ev(a[1],x,funcs)
 if op=='set':return frozenset(ev(b,x,funcs) for b in a[1])
 if op=='pair':return (ev(a[1],x,funcs),ev(a[2],x,funcs))
 if op=='call':return ev(funcs[a[1]],ev(a[2],x,funcs),funcs)
 b,c=ev(a[1],x,funcs),ev(a[2],x,funcs)
 return {'+':lambda:b+c,'-':lambda:max(0,b-c),'/':lambda:b//c,'%':lambda:b%c,'<':lambda:b<c}[op]()
def literal(a,b,e):
 D=frozenset(((u+v)//2,(u-v)//2) for u in range(a+1) for v in range(e,e+b+1) if (u-v)%2==0)
 S=[(s,t) for s in range(a-5,6) for t in range(e+b-5,e+6) if (s-t)%2==0]
 G=[frozenset(p for p in D if abs(p[0]+p[1]-s)==4 and p[0]-p[1]==t or abs(p[0]-p[1]-t)==4 and p[0]+p[1]==s) for s,t in S]
 G += [frozenset(p for p in D if p[0]+p[1]==q) for q in [0,a]]+[frozenset(p for p in D if p[0]-p[1]==q) for q in [e,e+b]]
 return D,S,G
def conn(T):
 if not T:return False
 seen={next(iter(T))};q=list(seen)
 for x,y in q:
  for p in [(x+1,y),(x-1,y),(x,y+1),(x,y-1)]:
   if p in T and p not in seen:seen.add(p);q.append(p)
 return seen==set(T)
C={(x,y) for x in range(-5,6) for y in range(-5,6) if abs(x)+abs(y)<=5 and (abs(x),abs(y))!=(2,2)}
assert len(C)==57 and conn(C)
for swap,sx,sy in itertools.product([0,1],[-1,1],[-1,1]):assert {(sx*(y if swap else x),sy*(x if swap else y)) for x,y in C}==C
cases=json.loads(Path('extracted/CASE-MAP.json').read_text());assert {tuple(c['triple']) for c in cases}=={(a,b,e) for a in range(1,11) for b in range(1,a+1) for e in range(2) if e==0 or a%2==b%2==0}
result=[]
for case in cases:
 a,b,e=case['triple'];D,S,G=literal(a,b,e);r=dict(triple=[a,b,e],kind=case['kind'],domain=len(D),centers=len(S))
 if case['kind']=='empty-group':assert frozenset() in G
 elif case['kind'].startswith('forced'):
  forced=set().union(*(g for g in G if len(g)==1));n=0;connected=0
  if len(forced)<=11:
   for k in range(12-len(forced)):
    for extra in itertools.combinations(D-forced,k):
     n+=1;T=forced|set(extra)
     if conn(T):connected+=1;assert not all(T&g for g in G)
  r.update(forced=len(forced),supersets=n,connected=connected)
 else:
  # All 31 actual formal table payloads, including selected group interfaces.
  module=case['origin'].removesuffix('Case');s=(F/(module+'Data.lean')).read_text();n=int(re.search(r'def point \(i : Fin (\d+)\)',s)[1]);k=4 if module=='Small' else int(re.search(r'rowOf (\d+) table',s)[1]);funcs={}
  for path in [F/(module+'Data.lean')]+sorted(F.glob(module+'Rows*.lean')):
   for name,expr in re.findall(r'^def (point|group|table|rows\d+) .*? := (.+)$',path.read_text(),re.M):funcs[name]=Parser(expr).parse()
  pts=[ev(funcs['point'],i,funcs) for i in range(n)];groups=[ev(funcs['group'],i,funcs) for i in range(k)]
  assert len(set(pts))==n and set(pts)==D;assert all(g in G for g in groups)
  rows=[ev(funcs['table'],m,funcs) for m in range(1<<k)] if module!='Small' else [sum(ev(Parser(re.search(r'^def value .*? := (.+)$',s,re.M)[1].replace('mask A','m')).parse(),{'m':m,'i.val':i},funcs)<<(6*i) for i in range(n)) for m in range(16)];vals=[[(r>>(6*i))&63 for i in range(n)] for r in rows];assert all(r>>(6*n)==0 for r in rows)
  assert all(0<=v<=12 for row in vals for v in row)
  adj=[(i,j) for i,p in enumerate(pts) for j,q in enumerate(pts) if abs(p[0]-q[0])+abs(p[1]-q[1])==1]
  for m in range(1,1<<k):
   for i,p in enumerate(pts):
    if all(p in groups[j] for j in range(k) if m>>j&1):assert vals[m][i]<=1
   for i,j in adj:assert vals[m][i]<=vals[m][j]+1
  # Independent exhaustive unordered disjoint masks; radix subtraction verified coordinatewise once via digits below.
  rep=sum(1<<(6*i) for i in range(n));tested=0
  for u in range(1,1<<k):
   a0=(u-1)&u
   while a0:
    b0=u^a0
    if a0<b0:
     # Each digit before packing lies in [19,55], so there is no borrow/carry.
     slack=rows[a0]+rows[b0]+31*rep-rows[u]
     assert all(vals[u][i]+1<=vals[a0][i]+vals[b0][i] for i in range(n))
     tested+=1
    a0=(a0-1)&u
  assert min(vals[-1])>=12
  r.update(module=module,vertices=n,labels=k,rows=len(rows),entries=n*len(rows),merge_pairs=tested)
 result.append(r);print(r,flush=True)
Path('exact-results.json').write_text(json.dumps(dict(status='PASS',seconds=time.monotonic()-start,cases=result),indent=2))
