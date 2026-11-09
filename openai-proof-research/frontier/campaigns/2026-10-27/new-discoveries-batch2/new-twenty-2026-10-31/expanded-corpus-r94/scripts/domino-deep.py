from dominolib import calc,D
import json,time
start=time.monotonic();out=[]
def parts(n,m):
 if not n:yield ();return
 for x in range(min(n,m),0,-1):
  for tail in parts(n-x,x):yield(x,)+tail
for n in range(10,25):
 count=0;bad=[]
 for lam in parts(n,n):
  if lam[0]+len(lam)-1>12 or sum(x>=i+1 for i,x in enumerate(lam))<2:continue
  for q in [2,3]:
   r=calc(lam,q);out.append(r);count+=1
   if any(r['remainders'])or not r['quotient_nonnegative']:bad.append(r);print('FAIL',r,flush=True)
  if time.monotonic()-start>105:break
 print('complete_size'if time.monotonic()-start<=105 else 'partial_size',n,'evaluations',count,'failures',len(bad),flush=True)
 (D/'outputs/domino-deep.json').write_text(json.dumps(out,indent=2)+'\n')
 if time.monotonic()-start>105:break
