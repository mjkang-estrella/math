"""Independent floating matrix eigendecomposition check; not part of the proof."""
import json
import math
from pathlib import Path
import numpy as np

Z=np.diag([1.,-1.])
S=np.array([[0.,1.],[1.,0.]])
U=2*math.pi*Z
V=math.pi*(-7*Z+math.sqrt(15)*S)/4
points=[np.zeros((2,2)),U,U+V,V]
K=np.zeros((8,8))
table=[]
for i in range(4):
    row=[]
    for j in range(4):
        eigen,Q=np.linalg.eigh(points[i]-points[j])
        cosine=Q@np.diag(np.cos(eigen))@Q.T
        K[2*i:2*i+2,2*j:2*j+2]=(np.eye(2)+cosine)/2-np.eye(2)/4
        row.append(float(cosine[0,0]))
    table.append(row)
y=np.array([1,0,-1,0,1,0,-1,0.])
q=float(y@K@y)
expected=math.cos(math.pi*math.sqrt(15))-3
assert abs(q-expected)<1e-12 and q < -2
result={'cos_scalar_table':table,'quadratic_form':q,'formula':'cos(pi sqrt15)-3',
        'expected':expected,'eigenvalues':np.linalg.eigvalsh(K).tolist(),'credit':0}
Path(__file__).with_name('numerical-check-replayed.json').write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps(result,indent=2))
