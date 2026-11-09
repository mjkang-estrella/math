from pathlib import Path
import random,json,itertools
L=Path(__file__).resolve().parent
def mult(E):return len(E)-len({x for x,y in E})-len({y for x,y in E})+1
def image(E,a,b):return {(a[x-1],b[y-1]) for x,y in E if a[x-1] and b[y-1]}
def graphs():
 maps=[(1,2,2),(0,2,3)]; rs=[(1,2,2),(0,2,1)]
 profiles={};examples={}
 for mask in range(1,512):
  E={(i//3+1,i%3+1) for i in range(9) if mask>>i&1}
  if len({x for x,y in E})<3 or len({y for x,y in E})<3:continue
  z=[]
  for a in maps:
   for b in rs:
    F=image(E,a,b)
    z.append(mult(F) if len({x for x,y in F})>1 and len({y for x,y in F})>1 else 0)
  key=(mult(E),*z);s=str(key);profiles[s]=profiles.get(s,0)+1;examples[s]=sorted(E)
 return dict(profiles=profiles,examples=examples)
def finite():
 rng=random.Random(241002032);obs={};viol=[];maxratio=(0,None);maxdelta=(0,None)
 for trial in range(110):
  directive=[rng.randrange(2) for _ in range(21)] if trial>10 else [int(c) for c in format(trial,'05b')]*4
  imgs=['1','2','3'];history=[]
  for s in directive:
   # Product is accumulated on the right, preserving the actual directive prefix.
   basis=['2','13','3'] if s==0 else ['1','2','13']
   imgs=[''.join(imgs[int(c)-1] for c in w) for w in basis];history.append(s)
   if sum(map(len,imgs))>90000:break
  factors={n:set() for n in range(1,47)}
  for n in factors:
   for w in imgs:factors[n].update(w[i:i+n] for i in range(len(w)-n+1))
  ps={n:len(v) for n,v in factors.items()}
  for n in range(1,46):
   if ps[n]>3*n:viol.append(dict(directive=history,n=n,p=ps[n]))
   if ps[n]/n>maxratio[0]:maxratio=(ps[n]/n,dict(directive=history,n=n,p=ps[n]))
   delta=ps[n+1]-ps[n]
   if delta>maxdelta[0]:maxdelta=(delta,dict(directive=history,n=n,p=ps[n],pnext=ps[n+1]))
   if n>32:continue
   for v in factors[n]:
    E={(int(a),int(b)) for a in '123' for b in '123' if a+v+b in factors[n+2]}
    if len({a for a,b in E})>1 and len({b for a,b in E})>1:
     key=str(sorted(E));obs[key]=obs.get(key,0)+1
 return dict(trials=110,max_n=46,source_counterexamples=viol,max_ratio=maxratio,max_delta=maxdelta,observed_extension_graphs=obs,warning='Finite prefix factors are lower bounds only. Neither absence nor finite first differences certify infinite languages.')
if __name__=='__main__':
 r=dict(graph_algebra=graphs(),finite_prefix_screen=finite());(L/'checks.json').write_text(json.dumps(r,indent=2));print(json.dumps({k:v for k,v in r['finite_prefix_screen'].items() if k!='observed_extension_graphs'}));print('graph profiles',len(r['graph_algebra']['profiles']))
