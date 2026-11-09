import pathlib,json,random,time,sys,itertools
sys.path.insert(0,str(pathlib.Path(__file__).resolve().parents[2]/'fresh-corpus-r14/.deps'))
import numpy as np
from scipy.optimize import linprog
from fractions import Fraction
D=pathlib.Path(__file__).resolve().parents[1]; rng=random.Random(int(sys.argv[1])); start=time.monotonic();counts={}; suspects=[]
for d in range(4,15):
 X=((np.arange(2**d)[:,None]>>np.arange(d))&1).astype(float)
 for rep in range(160):
  w=sorted(rng.randint(1,80) for _ in range(d))
  if sum(w)%2==0:w[-1]+=1
  scores=X@w; win=X[scores>sum(w)/2]
  # Full 2d nonnegative hyperplane cover, no assumed optimal orientation.
  A=np.concatenate([win,1-win],axis=1)
  res=linprog(np.ones(2*d),A_ub=-A,b_ub=-np.ones(len(win)),bounds=(0,None),method='highs')
  assert res.success
  delta=2-res.fun; inv=1/delta
  counts[d]=counts.get(d,0)+1
  if abs(inv-round(inv))>1e-6:
   r={'d':d,'w':w,'delta_float':delta,'reciprocal_float':inv,'cover':[str(Fraction(float(x)).limit_denominator(100000)) for x in res.x]}
   suspects.append(r);print('SUSPECT',r,flush=True)
   (D/'outputs/deficiency-suspect.json').write_text(json.dumps(r,indent=2)+'\n');break
  if time.monotonic()-start>105:break
 if suspects or time.monotonic()-start>105:break
print(json.dumps({'seed':sys.argv[1],'counts':counts,'suspects':suspects,'wall':time.monotonic()-start}),flush=True)
(D/'outputs'/('deficiency-'+sys.argv[1]+'.json')).write_text(json.dumps({'counts':counts,'suspects':suspects},indent=2)+'\n')
