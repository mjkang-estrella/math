"""Finite exploratory search, never a proof or an offline diagnostic."""
import json,pathlib,random,math
assert not pathlib.Path('frontier/sources/i141_intermittent_rate_permanence/seal.json').exists()
rng=random.Random(141)
complexes=[[2,1,0],[1,2,0],[0,2,1],[0,1,2],[1,0,2],[2,0,1]]
edges=[(i,(i+1)%6) for i in range(6)]+[((i+1)%6,i) for i in range(6)]
rows=[]
for case in range(12):
 order=list(range(12));rng.shuffle(order);x=[1-2e-5,1e-5,1e-5];maxmass=0.;positive=True;late=[]
 for period in range(60):
  for e in order:
   a,b=edges[e];v=[q-p for p,q in zip(complexes[a],complexes[b])];y=complexes[a]
   def f(z):
    flux=math.prod(w**p for w,p in zip(z,y));return [c*flux for c in v]
   for step in range(50):
    dt=.02;k1=f(x);k2=f([z+dt*k/2 for z,k in zip(x,k1)]);k3=f([z+dt*k/2 for z,k in zip(x,k2)]);k4=f([z+dt*k for z,k in zip(x,k3)])
    x=[z+dt*(a+2*b+2*c+d)/6 for z,a,b,c,d in zip(x,k1,k2,k3,k4)]
    positive=positive and min(x)>0;maxmass=max(maxmass,abs(sum(x)-1))
  if period>=40:late.append(min(x))
 rows.append(dict(order=order,final=x,late_period_minimum=min(late),late_period_last=late[-1],observed_positive=positive,max_observed_mass_error=maxmass))
s=pathlib.Path('frontier/sources/i141_intermittent_rate_permanence')
(s/'switch-search.json').write_text(json.dumps(dict(model='six degree-three complexes in reversible ring; total mass one',complexes=complexes,edges=edges,K=1,T=12,alpha=1,periods=60,seed=141,method='explicit RK4 step .02; no error certificate',rows=rows,scope='Numerical finite horizon only. Periodic schedule activates each directed edge once for duration one per period, so every sliding 12-window has each integral one exactly. No counterexample or eventual-bound proof follows.'),indent=2)+'\n')
print(json.dumps({'cases':len(rows),'all_observed_positive':all(r['observed_positive'] for r in rows),'least_late_min':min(r['late_period_minimum'] for r in rows),'max_mass_error':max(r['max_observed_mass_error'] for r in rows)}))
