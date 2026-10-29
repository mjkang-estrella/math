exec(open(__file__.replace('stationary.py','drum.py')).read().split('expr=')[0])
T=s.symbols('T',real=True)
J=s.simplify((gc*fz-gz*fc).subs(A,T)); H=s.simplify((gcc-gz*fcc/fz).subs(A,T));target=s.solve(J,T)[0]
HH=s.factor(H.subs(T,target));(P/'stationary-identities.txt').write_text('Stationary atan = '+str(s.factor(target))+'\nConstrained asymmetry at stationarity = '+str(HH)+'\n')
print((P/'stationary-identities.txt').read_text())
import numpy as np
from scipy.optimize import brentq
jf=s.lambdify((z,c),gc*fz-gz*fc,'numpy');hf=s.lambdify((z,c),gcc-gz*fcc/fz,'numpy');ff=s.lambdify((z,c),f,'numpy')
rows=[]
for zz in np.geomspace(.01,100,61):
 grid=np.linspace(.00001,.99999,181)
 for a,b in zip(grid,grid[1:]):
  if jf(zz,a)*jf(zz,b)<0:
   cc=brentq(lambda x:jf(zz,x),a,b);rows.append({'z':float(zz),'c':cc,'S_over_4pi':float(ff(zz,cc)),'H':float(hf(zz,cc))})
(P/'stationary-numerics.json').write_text(json.dumps(rows,indent=2));print('stationary branches',len(rows),'first',rows[:4])
