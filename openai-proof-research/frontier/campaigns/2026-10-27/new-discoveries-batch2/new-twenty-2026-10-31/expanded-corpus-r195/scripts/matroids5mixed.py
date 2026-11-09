import pathlib,json
D=pathlib.Path(__file__).resolve().parents[1]
s=(D/'scripts/matroids5.py').read_text();s=s[:s.index('# all X')];ns={'__file__':str(D/'scripts/matroids5.py')};exec(compile(s,str(D/'scripts/matroids5.py'),'exec'),ns);mats=ns['mats'];N=32;xs={}
for r,C in mats:
 for z in range(1<<len(C)):
  X=tuple(c for j,c in enumerate(C) if z>>j&1);xs.setdefault(X,[]).append(r)
out={'matroids':len(mats),'realizable_circuit_subfamilies':len(xs),'unique_maximal':0,'counterexamples':[]}
for X,rs in xs.items():
 top=[max(r[s] for r in rs) for s in range(N)]
 if top not in rs:continue
 out['unique_maximal']+=1;lens={0:0}
 for u in range(N):
  if u in lens:
   for x in X:
    if x&~u:lens[u|x]=max(lens.get(u|x,-1),lens[u]+1)
 v=[min((s|u).bit_count()-k for u,k in lens.items()) for s in range(N)]
 rules=[(a,b,a|b,max(min((a&b).bit_count(),x.bit_count()-1) for x in X if not((a&b)&~x))) for a in range(N) for b in range(a,N) if any(not((a&b)&~x) for x in X)]
 while True:
  old=v[:]
  for a,b,u,low in rules:v[u]=min(v[u],v[a]+v[b]-low)
  for a in range(N):
   for e in range(5):
    b=a|1<<e
    v[a]=min(v[a],v[b]);v[b]=min(v[b],v[a]+1)
  if v==old:break
 if v!=top:out['counterexamples'].append({'X':X,'v':v,'top':top})
print(out,flush=True);(D/'outputs/matroids5mixed.json').write_text(json.dumps(out,indent=2))
