import itertools,time,json,pathlib,sys
D=pathlib.Path(__file__).resolve().parents[1]
def le(u,v):return all(sorted(u[:k])<=sorted(v[:k]) if False else all(a<=b for a,b in zip(sorted(u[:k]),sorted(v[:k]))) for k in range(1,len(u)+1))
def graph(P):
 ix={p:i for i,p in enumerate(P)};G=[set() for p in P]
 for a,p in enumerate(P):
  for i in range(len(p)):
   for j in range(i):
    q=list(p);q[i],q[j]=q[j],q[i];b=ix.get(tuple(q))
    if b is not None:G[a].add(b)
 return G
class Limit(Exception):pass
def iso(G,target,deadline):
 n=len(G)
 def rec(c,d):
  if time.monotonic()>deadline:raise Limit
  while True:
   sig=lambda col:[(col[i],tuple(sorted(col[j] for j in G[i]))) for i in range(n)]
   a,b=sig(c),sig(d);keys={s:i for i,s in enumerate(sorted(set(a+b)))};cc=[keys[s] for s in a];dd=[keys[s] for s in b]
   if sorted(cc)!=sorted(dd):return False
   if len(set(cc))==len(set(c)):break
   c,d=cc,dd
  cells={v:[i for i,x in enumerate(cc) if x==v] for v in set(cc)}
  if len(cells)==n:return True
  v=min((v for v in cells if len(cells[v])>1),key=lambda v:len(cells[v]));x=cells[v][0];new=max(cc)+1
  for y in range(n):
   if dd[y]!=v:continue
   c1=cc.copy();d1=dd.copy();c1[x]=new;d1[y]=new
   if rec(c1,d1):return True
  return False
 c=[0]*n;d=[0]*n;c[0]=1;d[target]=1
 return rec(c,d)
out=[];began=time.monotonic();maxn=int(sys.argv[1]);start=int(sys.argv[2]) if len(sys.argv)>2 else 0;stop=int(sys.argv[3]) if len(sys.argv)>3 else 100000
for n in range(maxn,maxn+1):
 perms=list(itertools.permutations(range(n)));I={p:[u for u in perms if le(u,p)] for p in perms};count=0
 for wi,w in enumerate(perms):
  if not start<=wi<stop:continue
  if time.monotonic()-began>85:break
  P=I[w];G=graph(P);O=[];un=[]
  for v in range(len(P)):
   if len(G[v])!=len(G[0]):continue
   try:
    if iso(G,v,min(time.monotonic()+0.3,began+100)):O.append(P[v])
   except Limit:un.append(P[v])
  candidates=[v for v in P if set(I[v])==set(O)]
  row={'n':n,'index':wi,'w':w,'vertices':len(P),'orbit_size':len(O),'orbit':O,'unresolved_vertices':un,'interval_tops':candidates}
  out.append(row);count+=1
  (D/f'outputs/bruhat-{n}-{start}-{stop}.json').write_text(json.dumps(out,indent=2))
  if not candidates and not un:print('COUNTEREXAMPLE',row,flush=True);break
  if wi%10==0:print(n,wi,len(P),len(O),'unresolved',len(un),flush=True)
(D/f'outputs/bruhat-{n}-{start}-{stop}.json').write_text(json.dumps(out,indent=2));print('completed',count,'unresolved',sum(bool(x['unresolved_vertices']) for x in out))
