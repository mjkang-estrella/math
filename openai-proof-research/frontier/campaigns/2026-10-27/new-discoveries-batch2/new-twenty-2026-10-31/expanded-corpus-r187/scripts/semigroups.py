import pathlib,json
D=pathlib.Path(__file__).resolve().parents[1];level=[frozenset()];rows=[];hist=[{0:1}];hits=[]
for g in range(1,19):
 nxt=[];counts={}
 for gaps in level:
  f=max(gaps,default=0);m=next(x for x in range(1,g+2) if x not in gaps)
  for x in range(f+1,f+m+1):
   if x<1 or any(y not in gaps and x-y not in gaps for y in range(1,x//2+1)):continue
   ng=gaps|{x};nxt.append(ng);mult=next(y for y in range(1,g+2) if y not in ng);depth=(x+1+mult-1)//mult;counts[depth]=counts.get(depth,0)+1
 hist.append(counts);rows.append({'g':g,'total':len(nxt),'by_depth':counts});level=nxt
 if g>=2:
  for d in range(2,g+2):
   vals=[sum(c for q,c in hist[k].items() if q<=d) for k in [g,g-1,g-2]]
   if vals[0]<vals[1]+vals[2]:hits.append({'g':g,'d':d,'counts':vals})
 print(rows[-1],flush=True)
(D/'outputs/semigroups.json').write_text(json.dumps({'rows':rows,'hits':hits},indent=2))
