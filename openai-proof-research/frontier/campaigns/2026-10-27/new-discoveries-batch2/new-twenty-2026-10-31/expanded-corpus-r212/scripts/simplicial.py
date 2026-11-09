import itertools,sys,pathlib,json,time,math
D=pathlib.Path(__file__).resolve().parents[1];n,p=map(int,sys.argv[1:]);t=p-n
facets=list(itertools.combinations(range(p),n+1));rootfaces=[list(itertools.combinations(range(p),k+1)) for k in range(n+1)]
indexes=[{s:i for i,s in enumerate(ss)} for ss in rootfaces]
V=[sum(1<<v for v in f) for f in facets]
F=[[sum(1<<indexes[k][s] for s in itertools.combinations(f,k+1)) for f in facets] for k in range(1,n)]
R=[[indexes[n-1][s] for s in itertools.combinations(f,n)] for f in facets]
wanted=[t*math.comb(n,k)+math.comb(n,k+1) for k in range(1,n)];tested=matched=acyclic=disconnected=0;examples=[]
for inds in itertools.combinations(range(len(facets)),t):
 tested+=1;vs=0
 for i in inds:vs|=V[i]
 if vs.bit_count()!=p:continue
 good=False
 for j,fs in enumerate(F):
  u=0
  for i in inds:u|=fs[i]
  if u.bit_count()==wanted[j]:good=True;break
 if not good:continue
 matched+=1;par=list(range(t+len(rootfaces[n-1])));cyclic=False
 def find(a):
  while par[a]!=a:a=par[a]
  return a
 for a,i in enumerate(inds):
  for r in R[i]:
   x,y=find(a),find(t+r)
   if x==y:cyclic=True;break
   par[x]=y
  if cyclic:break
 if cyclic:continue
 acyclic+=1
 if any(find(i)!=find(0) for i in range(t)):
  disconnected+=1;ex=[facets[i] for i in inds];examples.append(ex)
  if len(examples)<=10:print('WITNESS',ex,flush=True)
row={'dimension':n,'vertices':p,'facets':t,'tested':tested,'face_count_matched':matched,'circuit_free':acyclic,'circuit_free_disconnected':disconnected,'examples':examples[:100],'scope':'current v3 Question 4.11 necessary search; not v1 simplicial-cycle theorem or full tree checker'}
(D/f'outputs/simplicial-{n}-{p}.json').write_text(json.dumps(row,indent=2)+'\n');print(json.dumps(row),flush=True)
