import pathlib,json,itertools,time
D=pathlib.Path(__file__).resolve().parents[1];n=5;N=1<<n;mats=[]
for rank in range(n+1):
 bs=[a for a in range(N) if a.bit_count()==rank]
 for mask in range(1,1<<len(bs)):
  B=[a for j,a in enumerate(bs) if mask>>j&1];Bset=set(B)
  if any(not any(((a^(1<<j))|1<<k) in Bset for k in range(n) if b>>k&1 and not a>>k&1) for a in B for b in B for j in range(n) if a>>j&1 and not b>>j&1):continue
  r=[max((a&s).bit_count() for a in B) for s in range(N)]
  C=[a for a in range(1,N) if r[a]<a.bit_count() and all(r[a^(1<<j)]==(a^(1<<j)).bit_count() for j in range(n) if a>>j&1)]
  mats.append((r,C))
# all X consisting of triples, and all X consisting of pairs: 1024+1024-1 cases
out={'matroids':len(mats),'families_examined':0,'nonempty':0,'unique_maximal':0,'counterexamples':[]}
for size in [2,3]:
 cs=[a for a in range(1,N) if a.bit_count()==size]
 for mask in range(1<<len(cs)):
  X=[a for j,a in enumerate(cs) if mask>>j&1];out['families_examined']+=1
  rs=[r for r,C in mats if all(x in C for x in X)]
  if not rs:continue
  out['nonempty']+=1;top=[max(r[s] for r in rs) for s in range(N)]
  if top not in rs:continue
  out['unique_maximal']+=1;lens={0:0}
  for u in range(N):
   if u in lens:
    for x in X:
     if x&~u:lens[u|x]=max(lens.get(u|x,-1),lens[u]+1)
  v=[min((s|u).bit_count()-k for u,k in lens.items()) for s in range(N)]
  lower=[min((a&b).bit_count(),min((x.bit_count()-1 for x in X if not((a&b)&~x)),default=100)) for a in range(N) for b in range(N)]
  while True:
   old=v[:]
   for a in range(N):
    for b in range(N):
     ab=a&b
     if any(not(ab&~x) for x in X):v[a|b]=min(v[a|b],v[a]+v[b]-lower[a*N+b])
     if not(a&~b):v[a]=min(v[a],v[b]);v[b]=min(v[b],v[a]+(b&~a).bit_count())
   if v==old:break
  if v!=top:out['counterexamples'].append({'X':X,'v':v,'top':top})
print(out,flush=True);(D/'outputs/matroids5.json').write_text(json.dumps(out,indent=2))
