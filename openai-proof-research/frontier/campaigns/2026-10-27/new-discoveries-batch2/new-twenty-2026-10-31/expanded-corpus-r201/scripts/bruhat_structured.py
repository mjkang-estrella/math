import pathlib,random,json,time,itertools
D=pathlib.Path(__file__).resolve().parents[1];ns={'__file__':str(D/'scripts/bruhat.py')};exec((D/'scripts/bruhat.py').read_text().split('out=[];began=')[0],ns);graph=ns['graph'];iso=ns['iso'];Limit=ns['Limit'];le=ns['le']
def interval(w):
 a=list(w);word=[]
 while any(a[i]>a[i+1] for i in range(len(a)-1)):
  i=next(i for i in range(len(a)-1) if a[i]>a[i+1]);word.append(i);a[i],a[i+1]=a[i+1],a[i]
 S={tuple(range(len(w)))}
 for i in reversed(word):
  T=set()
  for p in S:q=list(p);q[i],q[i+1]=q[i+1],q[i];T.add(tuple(q))
  S.update(T)
 return sorted(S)
rng=random.Random(201);choices=list(itertools.permutations(range(7)));rng.shuffle(choices);out=[];began=time.monotonic();eligible=0
for w in choices:
 if any(set(w[:i])==set(range(i)) for i in range(1,7)):continue
 inv=sum(w[i]>w[j] for i in range(7) for j in range(i+1,7))
 if not 8<=inv<=11:continue
 P=interval(w)
 if not 80<=len(P)<=220:continue
 eligible+=1
 if time.monotonic()-began>90 or len(out)>=60:break
 G=graph(P);O=[];un=[]
 for v in range(len(P)):
  if len(G[v])!=len(G[0]):continue
  try:
   if iso(G,v,min(time.monotonic()+.2,began+105)):O.append(P[v])
  except Limit:un.append(P[v])
 tops=[v for v in O if all(le(u,v) for u in O)];valid=[v for v in tops if set(interval(v))==set(O)]
 r={'w':w,'vertices':len(P),'inversions':inv,'orbit_size':len(O),'orbit':O,'unresolved_vertices':un,'interval_tops':valid};out.append(r)
 (D/'outputs/bruhat-structured7.json').write_text(json.dumps(out,indent=2))
 print(len(out),w,len(P),len(O),'unresolved',len(un),flush=True)
 if not valid and not un:print('COUNTEREXAMPLE',r);break
print('completed',len(out),'eligible_seen',eligible)
