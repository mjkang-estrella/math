import pathlib,json,itertools
D=pathlib.Path(__file__).resolve().parents[1];n=4;N=1<<n; mats=[]
for f in range(1,1<<N,2):
 I=[a for a in range(N) if f>>a&1]
 if any(not(f>>(a^(1<<j))&1) for a in I for j in range(n) if a>>j&1):continue
 if any(not any((b>>j&1) and not(a>>j&1) and (f>>(a|1<<j)&1) for j in range(n)) for a in I for b in I if a.bit_count()<b.bit_count()):continue
 r=[max(a.bit_count() for a in I if a&s==a) for s in range(N)]
 C=[a for a in range(1,N) if not(f>>a&1) and all(f>>(a^(1<<j))&1 for j in range(n) if a>>j&1)]
 mats.append((r,C))
xs={}
for r,C in mats:
 for z in range(1<<len(C)):
  X=tuple(c for j,c in enumerate(C) if z>>j&1);xs.setdefault(X,[]).append(r)
counts={'matroids':len(mats),'circuit_families':len(xs),'unique_maximal':0,'counterexamples':[]}
for X,rs in xs.items():
 top=[max(r[s] for r in rs) for s in range(N)]
 if top not in rs:continue
 counts['unique_maximal']+=1
 # dynamic proper sequences: maximal sequence length with given union
 lens={0:0}
 for u in range(N):
  if u not in lens:continue
  for x in X:
   if x&~u:lens[u|x]=max(lens.get(u|x,-1),lens[u]+1)
 v=[min((s|u).bit_count()-k for u,k in lens.items()) for s in range(N)]
 while True:
  old=v[:]
  for a in range(N):
   for b in range(N):
    ab=a&b
    for x in X:
     if not(ab&~x):v[a|b]=min(v[a|b],v[a]+v[b]-min(ab.bit_count(),x.bit_count()-1))
    if not(a&~b):v[a]=min(v[a],v[b]);v[b]=min(v[b],v[a]+(b&~a).bit_count())
  if v==old:break
 if v!=top:counts['counterexamples'].append({'X':X,'v':v,'top':top})
print(counts);(D/'outputs/matroids.json').write_text(json.dumps(counts,indent=2))
