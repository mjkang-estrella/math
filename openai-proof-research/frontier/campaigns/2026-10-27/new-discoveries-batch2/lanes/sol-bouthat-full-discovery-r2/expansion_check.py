import os
os.environ.update(OPENBLAS_NUM_THREADS='1',OMP_NUM_THREADS='1',MKL_NUM_THREADS='1')
import resource
resource.setrlimit(resource.RLIMIT_AS,(512*1024**2,512*1024**2))
resource.setrlimit(resource.RLIMIT_CPU,(100,100))
from fractions import Fraction as F
from pathlib import Path
import json
rows=[]
for m in range(21):
 def h(x): return x**m/(1-F(3,2)*x+x*x)**(m+1)
 def sums(n):
  common=sum((h(F(k,n)) for k in range(1,n)),F(0))/n
  return common+h(F(0))/n,common+h(F(1))/n
 old=sums(1);mins=[None,None];fail=[]
 for n in range(1,61):
  new=sums(n+1);d=[new[0]-old[0],old[1]-new[1]]
  for j in range(2):
   if mins[j] is None or d[j]<mins[j][0]:mins[j]=(d[j],n)
   if d[j]<0:fail.append({'n':n,'sequence':['L','R'][j],'difference':str(d[j])})
  old=new
 rows.append({'m':m,'n_max':60,'failures':fail,'minimum_signs':[int(v[0]>0)-int(v[0]<0) for v in mins]})
 print(m,len(fail),flush=True)
Path(__file__).with_name('expansion-checks.json').write_text(json.dumps({'arithmetic':'exact rational','proof':False,'rows':rows},indent=2))
