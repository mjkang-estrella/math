import itertools as it,pathlib,json
D=pathlib.Path(__file__).resolve().parents[1];mons=[a for a in it.product(range(4),repeat=3) if sum(a)==3];pts=list(it.product(range(3),repeat=3));total=0;full=0;unresolved=[]
def det(a):return a[0][0]*(a[1][1]*a[2][2]-a[1][2]*a[2][1])-a[0][1]*(a[1][0]*a[2][2]-a[1][2]*a[2][0])+a[0][2]*(a[1][0]*a[2][1]-a[1][1]*a[2][0])
for mask in range(1,1<<10):
 terms=[a for k,a in enumerate(mons) if mask>>k&1];total+=1
 def hessian(x):
  ans=[]
  for i in range(3):
   row=[]
   for j in range(3):
    v=0
    for a in terms:
     b=list(a);c=b[i];b[i]-=1
     if c==0:continue
     c*=b[j];b[j]-=1
     if c:v+=c*__import__('math').prod(x[k]**b[k] for k in range(3))
    row.append(v)
   ans.append(row)
  return ans
 if any(det(hessian(x)) for x in pts):full+=1
 else:unresolved.append(mask)
(D/'outputs/search-wlp.json').write_text(json.dumps(dict(id=58,space='all1023 nonzero ternary homogeneous cubics with coefficients0/1, all evaluation triples0/1/2 until nonzero Hessian determinant; remaining masks include embedding dimension<3, not asserted counterexamples',tested=total,nonzero_hessian=full,unresolved_masks=unresolved),indent=2)+'\n')
