from finite import *
forms=[]
for mask in range(128):
 def f(x,y):
  a=[(x>>i)&1 for i in range(3)];b=[(y>>i)&1 for i in range(3)]
  vals=[a[i]*b[i] for i in range(3)]+[a[i]*b[j] for i,j in [(0,1),(0,2),(1,2)]]+[a[0]*a[1]*b[2]^a[0]*b[1]*a[2]^b[0]*a[1]*a[2]]
  return sum(v*((mask>>i)&1) for i,v in enumerate(vals))%2
 F=[f(x,y) for x,y in it.product(range(8),repeat=2)]
 t=[[(x^y)+8*((s^u)^F[x*8+y]) for y,u in it.product(range(8),range(2))] for x,s in it.product(range(8),range(2))]
 # encode coordinates consistently as 2*x+s
 t=[[2*(x^y)+(s^u^F[x*8+y]) for y,u in it.product(range(8),range(2))] for x,s in it.product(range(8),range(2))]
 assert moufang(t)
 forms.append(F)
# Include every normalized central coboundary g, all 2^7 functions on F2^3 with g(0)=0.
weights=[]
for m,F in enumerate(forms):
 for g in range(128):
  G=[0]+[(g>>(x-1))&1 for x in range(1,8)]
  w=sum(F[x*8+y]^G[x]^G[y]^G[x^y] for x,y in it.product(range(8),repeat=2))
  weights.append((w*4,m,g))
nontrivial=[v for v in weights if v[1]&64]
best=min(nontrivial)
save('code-loops-small.json',dict(source='Central extension code-loop ansatz; source associator definition (xy)z=x(yz)[x,y,z]. All 128 multiplication tables directly satisfy Moufang identity.',order=16,cochain_parameters=128,coboundaries=128,difference_cochains_tested=len(weights),min_distance_nonequivalent_associator=best,threshold=96,note='Only center-preserving coordinate comparisons within this ansatz. Not all relabelings and not all Moufang loops. Cubic bit gives nonzero associator versus zero; all nonzero alternating 3-forms in dimension3 equivalent. Distance 64 is below 96: potential violation of Conjecture11.2, requiring prior-art and source-scope investigation.'))
