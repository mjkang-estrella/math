import pathlib,json,hashlib,sys,re,collections,time,resource
L=pathlib.Path(__file__).resolve().parent;R=L.parent/'sol-floor-sums-breadth-depth-r241'
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
bindings=json.loads((L/'bindings.json').read_text())
# Extend freeze before opening the predecessor scientific body.
for name in ['sources/pong11.pdf','sources/pong11.txt']:
 p=R/name;q=L/'frozen'/name;q.parent.mkdir(exist_ok=True)
 if not any(x['original']==str(p) for x in bindings['files']):
  h=sha(p);q.write_bytes(p.read_bytes());assert sha(q)==h==sha(p)
  bindings['files'].append(dict(original=str(p),copy=str(q.relative_to(L)),sha256=h,size=p.stat().st_size))
(L/'bindings.json').write_text(json.dumps(bindings,indent=2))
for x in bindings['files']:assert sha(pathlib.Path(x['original']))==sha(L/x['copy'])==x['sha256']
admin={}
for n in ['ledger.json','prior-campaign-context.json']:
 d=json.loads((L/'administrative'/n).read_text());admin[n]={'keys':list(d),'entries':len(d.get('accepted',[])),'counts':{k:d.get(k) for k in ['accepted_count','total_accepted_count','next_global_outcome_number']}}
(L/'administrative/read.json').write_text(json.dumps(admin,indent=2))
# Tokenization and syntax parsing do not expand lets. Atoms are interned.
def parse(s):
 stack=[];roots=[]
 for m in re.finditer(r';[^\n]*|\(|\)|[^\s()]+',s):
  t=m.group()
  if t.startswith(';'):continue
  if t=='(':stack.append([])
  elif t==')':
   assert stack
   x=stack.pop()
   (stack[-1] if stack else roots).append(x)
  else:(stack[-1] if stack else roots).append(sys.intern(t))
 assert not stack
 return roots
sys.setrecursionlimit(12000)
nodes=[];cache={}
def node(x):
 if x not in cache:cache[x]=len(nodes);nodes.append(x)
 return cache[x]
class Env:
 def __init__(self,d=None,parent=None):self.d=d or {};self.parent=parent
 def get(self,k):
  e=self
  while e is not None:
   if k in e.d:return e.d[k]
   e=e.parent
  return None
def resolve(x,e):
 if isinstance(x,str):
  v=e.get(x);return node(x) if v is None else v
 if x and x[0]=='let':
  assert len(x)==3
  names=[v[0] for v in x[1]];assert len(set(names))==len(names)
  # SMT-LIB let bindings are simultaneous, not sequential.
  d={v[0]:resolve(v[1],e) for v in x[1]}
  return resolve(x[2],Env(d,e))
 return node(tuple(resolve(v,e) for v in x))
def head(i):
 x=nodes[i]
 if isinstance(x,str):return x
 return head(x[0]) if x else 'EMPTY'
def fmt(i,limit=300):
 x=nodes[i]
 if isinstance(x,str):return x
 s='('+' '.join(fmt(v,limit) for v in x)+')'
 return s if len(s)<=limit else s[:limit]+'...'
start=time.monotonic()
ast=parse((L/'frozen/z3-proof.sexpr').read_text());assert len(ast)==1
root=resolve(ast[0],Env());del ast
# All reachable expressions: no unused let bindings are counted as proof dependencies.
seen=set();todo=[root]
while todo:
 i=todo.pop()
 if i in seen:continue
 seen.add(i);x=nodes[i]
 if isinstance(x,tuple):todo.extend(x)
hist=collections.Counter(head(i) for i in seen if isinstance(nodes[i],tuple))
(L/'dag.jsonl').write_text(''.join(json.dumps({'id':i,'atom':x} if isinstance(x,str) else {'id':i,'args':x})+'\n' for i,x in enumerate(nodes)))
(L/'dag-index.json').write_text(json.dumps({'root':root,'nodes':len(nodes),'reachable':len(seen),'heads':dict(hist),'root_head':head(root)},indent=2))
print(json.dumps({'root':root,'nodes':len(nodes),'heads':dict(hist)}))
(L/'parse-receipt.json').write_text(json.dumps({'seconds':time.monotonic()-start,'maxrss_KiB':resource.getrusage(resource.RUSAGE_SELF).ru_maxrss,'capture':'simultaneous lexical let, shared DAG, no solver imports'},indent=2))
