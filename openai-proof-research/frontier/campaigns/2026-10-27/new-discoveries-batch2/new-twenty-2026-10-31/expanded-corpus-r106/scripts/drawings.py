import random,json
rng=random.Random(106358422)
def orient(a,b,c):return (b[0]-a[0])*(c[1]-a[1])-(b[1]-a[1])*(c[0]-a[0])
def cross(a,b,c,d):return orient(a,b,c)*orient(a,b,d)<0 and orient(c,d,a)*orient(c,d,b)<0
def triang(P):
 if sum(P[i][0]*P[(i+1)%len(P)][1]-P[i][1]*P[(i+1)%len(P)][0] for i in range(len(P)))<0:P=P[::-1]
 Q=P.copy();diags=0
 while len(Q)>3:
  for i in range(len(Q)):
   a,b,c=Q[i-1],Q[i],Q[(i+1)%len(Q)]
   if orient(a,b,c)>0 and not any(orient(a,b,p)>0 and orient(b,c,p)>0 and orient(c,a,p)>0 for p in Q if p not in [a,b,c]):
    Q.pop(i);diags+=1;break
  else:return False
 return diags==len(P)-3
out=[]
for n in range(11,31):
 passed=0
 for trial in range(200):
  while True:
   P=rng.sample([(i,j) for i in range(101) for j in range(101)],n)
   if all(orient(P[i],P[j],P[k]) for i in range(n) for j in range(i+1,n) for k in range(j+1,n)):break
  # deterministic 2-opt decreases Euclidean perimeter at each crossing swap
  while True:
   found=False
   for i in range(n):
    for j in range(i+2,n):
     if (j+1)%n==i:continue
     if cross(P[i],P[(i+1)%n],P[j],P[(j+1)%n]):P[i+1:j+1]=reversed(P[i+1:j+1]);found=True;break
    if found:break
   if not found:break
  assert triang(P);passed+=1
 out.append({'n':n,'simple_geometric_Hamiltonian_cycles_tested':passed,'extensions_to_2n_minus3':passed})
open('outputs/drawings.json','w').write(json.dumps(out,indent=2));print(out)
