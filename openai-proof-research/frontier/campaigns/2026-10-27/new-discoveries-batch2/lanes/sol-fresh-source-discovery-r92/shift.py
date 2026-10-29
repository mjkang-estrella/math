from pathlib import Path
from itertools import product
import json
L=Path(__file__).resolve().parent
for inner in product(range(1,10),repeat=3):
 a=[0,1,*inner,1,0];b=[a[k]+a[k+1] for k in range(len(a)-1)]
 if all(b[k]**2>=b[k-1]*b[k+1] for k in range(1,len(b)-1)) and any(a[k]**2<a[k-1]*a[k+1] for k in range(2,len(a)-2)):
  (L/'shift-results.json').write_text(json.dumps({'a':a,'b':b,'identity':'b[k]=a[k]+a[k+1]','LC_a_fails':[k for k in range(2,len(a)-2) if a[k]**2<a[k-1]*a[k+1]]},indent=2));break
else:raise AssertionError('no diagnostic')
print((L/'shift-results.json').read_text())
