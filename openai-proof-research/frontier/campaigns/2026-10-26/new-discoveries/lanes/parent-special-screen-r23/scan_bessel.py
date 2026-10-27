import numpy as np
from scipy.special import jn_zeros,j0
from pathlib import Path
import json
zs=jn_zeros(0,1500);hits=[];mins=[]
for M in list(range(1,81))+[100,200,500,1000,1500]:
 x=np.unique(np.r_[np.linspace(0,1,5001),1-np.geomspace(1e-10,0.01,400)])
 mat=j0(np.outer(x,zs[:M]))
 for a in [0.,.1,.25,.4,.49,.5]:
  v=mat@((1-np.arange(1,M+1)/(M+1))*zs[:M]**a)
  idx=np.argmin(v[:-1]);mn=float(v[:-1][idx]);arg=float(x[:-1][idx])
  mins.append([M,a,mn,arg])
  if mn < -1e-8:hits.append(mins[-1]);print('HIT',mins[-1],flush=True)
 if M%20==0:print('done',M,flush=True)
Path(__file__).with_name('bessel-scan.json').write_text(json.dumps({'numerical_only':True,'nonendpoint_minima':mins,'hits':hits},indent=2)+'\n')
print('hits',len(hits),flush=True)
