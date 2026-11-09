from pathlib import Path
from fractions import Fraction as F
import json
L=Path(__file__).parent;c=json.loads((L/'frozen/sol-quantile-aggregation-full-r1/certificate.json').read_text())
d=list(map(F,c['dual']));p=c['old_permutation'];print('dual',[(i,str(d[i])) for i in range(0,200,10)])
print('dual slope runs')
last=None
for i in range(199):
 s=d[i+1]-d[i]
 if s!=last: print(i,str(s));last=s
print('permutation translation runs')
last=None
for i,j in enumerate(p):
 if j-i!=last:print(i,j-i);last=j-i
