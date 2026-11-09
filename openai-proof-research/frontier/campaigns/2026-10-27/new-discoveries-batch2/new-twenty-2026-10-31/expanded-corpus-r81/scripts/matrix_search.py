from pathlib import Path
import re,json,itertools,numpy as np
from scipy.optimize import minimize
D=Path(__file__).resolve().parents[1];t=(D/'sources/2501.02563.txt').read_text();a=t.index(' T=\\begin{pmatrix}');b=t.index('\\end{pmatrix}',a);s=t[a:b].split('\\begin{pmatrix}')[1];T=np.array([[int(x) for x in row.strip().split('&')] for row in s.strip().split('\\\\')],float);assert T.shape==(11,11) and np.array_equal(T,T.T) and np.all(T[-1]==0)
(D/'outputs/T.json').write_text(json.dumps(T.astype(int).tolist(),indent=2)+'\n');T=T[:10,:10]
def val(w):
 w=np.array(w,float);z=np.sqrt(w/w.sum());return float(np.linalg.eigvalsh(T*z[:,None]*z[None,:])[1])
best=(1,None);count=0
for w in itertools.product(range(3),repeat=10):
 if sum(w)<2:continue
 v=val(w);count+=1
 if v<best[0]:best=(v,w)
print('exhaustive',count,best,flush=True)
rng=np.random.default_rng(810366516);rows=[]
for k in range(40):
 w=rng.dirichlet(np.full(10,.3 if k<20 else 1.));res=minimize(val,w,method='SLSQP',bounds=[(0.,1.)]*10,constraints=[{'type':'eq','fun':lambda w:sum(w)-1}],options={'maxiter':250,'ftol':1e-12});rows.append({'run':k,'fun':float(res.fun),'success':bool(res.success),'w':res.x.tolist()})
out={'source':'2501.02563 Theorem 4.6 displayed T and Conjecture 4.7','exhaustive_space':'x_1..x_10 in {0,1,2}; total >=2; x_11=0','count':count,'minimum':best,'optimization':rows,'limits':'Floating-point diagnostics only. Zero added coordinate cannot lower ratio; nonzero blowup spectrum given by diag(sqrt x) T diag(sqrt x), plus zeros. No certified eigenvalue isolation or Lean bridge.'};(D/'outputs/matrix-search.json').write_text(json.dumps(out,indent=2)+'\n');print('continuous best',min(r['fun'] for r in rows))
