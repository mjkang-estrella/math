import json,sys
import numpy as np
from scipy.special import airy
from scipy.integrate import simpson
from pathlib import Path
L=Path(__file__).resolve().parent
# Exploratory Fourier inversion ONLY; no interval enclosure or theorem certificate.
c=2**(-1/3)
outputs=[]
for N,T in [(20001,35.),(40001,45.)]:
 u=np.linspace(0,T,N);F=airy(1j*c*u)[0]; inv=1/F
 rows=[]
 for x in np.linspace(-1.,1.,81):
  a=inv*np.exp(-1j*u*x)
  g=np.array([simpson(np.real(a*(-1j*u)**k),x=u)/np.pi for k in range(5)])
  score=g[1]/g[0];v=score**2-g[2]/g[0]
  vp=-g[3]/g[0]+3*g[2]*g[1]/g[0]**2-2*score**3
  vpp=-g[4]/g[0]+4*g[3]*g[1]/g[0]**2+3*(g[2]/g[0])**2-12*g[2]*g[1]**2/g[0]**3+6*score**4
  rows.append({'x':float(x),'g':g.tolist(),'v':float(v),'vp':float(vp),'vpp':float(vpp)})
 w0=2*rows[40]['v']
 for i,row in enumerate(rows):row['w']=row['v']+rows[80-i]['v'];row['w_minus_w0']=row['w']-w0
 outputs.append({'N':N,'T':T,'w0':w0,'rows':rows,'minimum_vpp':min(r['vpp'] for r in rows)})
(L/'airy-diagnostics.json').write_text(json.dumps(outputs,indent=2))
print(json.dumps({'diagnostics_only':True,'w0':[o['w0'] for o in outputs], 'min_vpp':[o['minimum_vpp'] for o in outputs],'max_grid_discrepancy':max(abs(a['w']-b['w']) for a,b in zip(outputs[0]['rows'],outputs[1]['rows']))}))
