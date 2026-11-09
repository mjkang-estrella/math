import pathlib,json,itertools,sys
D=pathlib.Path(__file__).resolve().parents[1];N=int(sys.argv[1]);types={1:[()]};sizes={():1}
def multisets(options,weight,start=0):
 if weight==0:yield ();return
 for j in range(start,len(options)):
  o,w=options[j]
  if w<=weight:
   for rest in multisets(options,weight-w,j):yield (o,)+rest
for n in range(2,N+1):
 opts=[(t,s) for s in range(1,n) for t in types[s]]
 edges=[]
 for w in range(1,n):edges += [(e,w) for e in multisets(opts,w)]
 types[n]=list(multisets(edges,n-1));
 for t in types[n]:sizes[t]=n
 print('rooted',n,len(types[n]),flush=True)
def unpack(t):
 es=[];count=1
 def f(t,r):
  nonlocal count
  for edge in t:
   e=[r]
   for ch in edge:
    v=count;count+=1;e.append(v);f(ch,v)
   es.append(tuple(e))
 f(t,0);return tuple(sorted(es))
def canonical(es,n):
 inc=[[] for _ in range(n)]
 for e in es:
  for v in e:inc[v].append(e)
 def code(v,parent):return tuple(sorted(tuple(sorted(code(w,e) for w in e if w!=v)) for e in inc[v] if e!=parent))
 return min(code(v,None) for v in range(n))
def balanced_label(es,n,k):
 low=n//k;high=(n+k-1)//k;m=len(es);lo=m//k;hi=(m+k-1)//k
 inc=[[] for _ in range(n)]
 for e in es:inc[max(e)].append(e)
 lab=[0]*n;vc=[0]*k;ec=[0]*k;trials=0
 def dfs(v):
  nonlocal trials
  trials+=1
  if v==n:return min(vc)>=low and min(ec)>=lo
  for a in range(k if v else 1):
   if vc[a]>=high:continue
   lab[v]=a;vals=[sum(lab[x] for x in e)%k for e in inc[v]]
   for z in vals:ec[z]+=1
   vc[a]+=1
   ok=max(ec)<=hi and sum(max(0,low-c) for c in vc)<=n-v-1
   if ok and dfs(v+1):return True
   vc[a]-=1
   for z in vals:ec[z]-=1
  return False
 return dfs(0),trials
out=[]
for n in range(2,N+1):
 seen=set();space=[]
 for t in types[n]:
  es=unpack(t);c=canonical(es,n)
  if c not in seen:seen.add(c);space.append(es)
 for k in range(2,9):
  bad=[];trials=0
  for es in space:
   ok,tr=balanced_label(es,n,k);trials+=tr
   if not ok:bad.append(es)
  r={'n':n,'k':k,'nonisomorphic_hypertrees':len(space),'label_dfs_nodes':trials,'failures':bad};out.append(r);print(r,flush=True)
  (D/f'outputs/hypertrees-{N}.json').write_text(json.dumps(out,indent=2))
