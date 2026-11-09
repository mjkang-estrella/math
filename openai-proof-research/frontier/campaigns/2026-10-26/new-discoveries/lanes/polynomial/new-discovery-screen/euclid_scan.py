from pathlib import Path
import sys,json,time
sys.path.insert(0,str(Path(__file__).resolve().parent.parent/'.pydeps'))
from flint import fmpz_poly
f=fmpz_poly([1,1]); start=time.time()
for k in range(1,15):
 a=[int(x) for x in f.coeffs()]
 bad_lc=[i for i in range(2,len(a)-1) if a[i]*a[i]<a[i-1]*a[i+1]]
 decreasing=False;viol=[]
 for i in range(1,len(a)):
  if a[i]<a[i-1]:decreasing=True
  elif a[i]>a[i-1] and decreasing:viol.append(i)
 print(json.dumps({'k':k,'degree':f.degree(),'unimodal':not viol,'turn_violations':viol[:10],'tail_lc_violations':bad_lc[:10],'maxbits':max(a).bit_length(),'peak':a.index(max(a)),'seconds':time.time()-start}),flush=True)
 if viol:
  Path(__file__).with_name('euclid-counterexample.json').write_text(json.dumps({'k':k,'coefficients':a,'violations':viol}));break
 f=f*f-f+1
