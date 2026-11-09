import itertools,json
# Full reflexive commuting moments; central deletion is performed by polynomial expansion.
def moments(P):
 def compose(a,b):return tuple(a[b[i]] for i in range(len(a)))
 C=[[compose(a,b)==compose(b,a) for b in P] for a in P];g=len(P);c=[sum(r) for r in C];z=sum(v==g for v in c)
 s1=sum(c);s2=sum(v*v for v in c);q=sum(c[i]*c[j] for i in range(g) for j in range(g) if C[i][j]);return [g,z,s1,s2,q]
def permgroup(n,even=False):
 return [p for p in itertools.permutations(range(n)) if not even or sum(p[i]>p[j] for i in range(n) for j in range(i+1,n))%2==0]
def dih(n):return list({tuple((s*i+b)%n for i in range(n)) for s in [-1,1] for b in range(n)})
bases={f'S{n}':moments(permgroup(n)) for n in [3,4,5]};bases.update({f'A{n}':moments(permgroup(n,True)) for n in [4,5]});bases.update({f'D{2*n}':moments(dih(n)) for n in [4,5,6,7,8,9,10]})
# On X=G-Z: T_j=sum(c-z)^j and Qx=sum_comm (c-z)(d-z).
# full sum_comm (c-z)(d-z) = q - 2*z*s2 + z*z*s1.
# remove ordered pairs touching center, add central-central overlap.
def gaps(v):
 g,z,s1,s2,q=v;n=g-z
 t1=s1-2*z*g+z*z
 t2=s2-2*z*s1-z*g*g+3*z*z*g-z**3
 qx=q-2*z*s2+z*z*s1-2*z*(g-z)*(s1-z*g)+z*z*(g-z)**2
 L=n*qx-(t1+2*n)*t2+2*t1*t1
 U=(n*n+t1)*t2-n*t1*t1-n*qx
 return L,U
out={'base_moments':bases,'cases':0,'negative':[],'max_group_order':0}
keys=list(bases)
for k in range(1,7):
 for inds in itertools.combinations_with_replacement(range(len(keys)),k):
  v=[1]*5
  for j in inds:v=[a*b for a,b in zip(v,bases[keys[j]])]
  L,U=gaps(v);out['cases']+=1;out['max_group_order']=max(out['max_group_order'],v[0])
  if L<0 or U<0:out['negative'].append({'factors':[keys[j] for j in inds],'moments':v,'gaps':[L,U]})
open('outputs/group-products.json','w').write(json.dumps(out,indent=2));print({k:v for k,v in out.items() if k!='base_moments'})
