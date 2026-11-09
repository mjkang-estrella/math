import pathlib,json,itertools,random,time,sys
D=pathlib.Path(__file__).resolve().parents[1]
def adj(n,E):
 a=[set() for _ in range(n)]
 for u,v in E:a[u].add(v);a[v].add(u)
 return a
def solve(a,k,cf=None,equitable=False,pre=None,cap=100000):
 n=len(a);c=[-1]*n;counts=[0]*k;nodes=0
 for v,z in (pre or {}).items():c[v]=z;counts[z]+=1
 def rec(left):
  nonlocal nodes
  nodes+=1
  if nodes>cap:raise TimeoutError
  if cf:
   for s in cf:
    if all(c[v]>=0 for v in s) and s and not any(sum(c[v]==z for v in s)==1 for z in set(c[v] for v in s)):return False
  if equitable and any(t>(n+k-1)//k for t in counts):return False
  if not left:return not equitable or max(counts)-min(counts)<=1
  v=max(left,key=lambda v:(len({c[w] for w in a[v] if c[w]>=0}),len(a[v])))
  forbidden={c[w] for w in a[v]}; used=max(c,default=-1)
  for z in range(min(k,used+2)):
   if z in forbidden:continue
   c[v]=z;counts[z]+=1
   if rec(left-{v}):return True
   counts[z]-=1;c[v]=-1
  return False
 try:return rec({v for v in range(n) if c[v]<0}),nodes
 except TimeoutError:return None,nodes

def graphs(mode):
 for n in range(1,6):
  pairs=list(itertools.combinations(range(n),2))
  for mask in range(1<<len(pairs)):yield n,[e for j,e in enumerate(pairs) if mask>>j&1],f'all-labelled-{n}-{mask}'
 r=random.Random(169)
 for n in range(6,15):
  for j in range(160):
   p=r.choice([.15,.25,.4,.5,.7,.85]); E=[(u,v) for u,v in itertools.combinations(range(n),2) if r.random()<p]
   yield n,E,f'random-{n}-{j}'

def run(mode):
 out={'mode':mode,'seed':169,'tested':0,'by_order':{},'unknown':[],'counterexamples':[],'max_nodes':0};start=time.monotonic()
 for n,E,key in graphs(mode):
  if time.monotonic()-start>100:out['stop']='100s internal cap';break
  a=adj(n,E);delta=max(map(len,a),default=0)
  if mode=='pcf':
   if delta<3:continue
   b=a;cf=[s for s in a if s];k=delta+1;eq=False
  elif mode=='pocf':
   b=adj(len(E),[(i,j) for i,j in itertools.combinations(range(len(E)),2) if set(E[i])&set(E[j])]);cf=[s for s in b if s];k=delta+3;eq=False
  elif mode=='total':
   N=n+len(E);edges=E+[(u,n+i) for i,e in enumerate(E) for u in e]+[(n+i,n+j) for i,j in itertools.combinations(range(len(E)),2) if set(E[i])&set(E[j])];b=adj(N,edges);cf=None;k=delta+2;eq=True
  else:raise ValueError
  yes,nodes=solve(b,k,cf,eq,cap=15000)
  out['tested']+=1;out['by_order'][str(n)]=out['by_order'].get(str(n),0)+1;out['max_nodes']=max(nodes,out['max_nodes'])
  if yes is None:out['unknown'].append(key)
  if yes is False:out['counterexamples'].append({'key':key,'n':n,'edges':E});print(out['counterexamples'][-1],flush=True);break
  (D/f'outputs/{mode}.json').write_text(json.dumps(out,indent=2))
 out['wall_seconds']=time.monotonic()-start;(D/f'outputs/{mode}.json').write_text(json.dumps(out,indent=2));print(out)
if __name__=='__main__':run(sys.argv[1])
