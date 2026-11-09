import pathlib,json,itertools,math,fractions
P=pathlib.Path(__file__).parent;out={}
a=[]
for n in range(3,9):
 s=sum(sum(p[p[i]]>p[p[i+1]] for i in range(n-1)) for p in itertools.permutations(range(n)))
 v=fractions.Fraction(s,math.factorial(n));target=fractions.Fraction(n-1,2)-fractions.Fraction(2,n);assert v==target
 a.append(dict(n=n,total_descent_sum=s,permutations=math.factorial(n),expectation=str(v),target=str(target)))
out['363527']=dict(executed=a,limit='finite corroboration only; successor Theorem1.1 gives n>=5 at k2; direct n3,4 close the two remaining cases')
def det(a):
 a=[r[:] for r in a];prev=1;sgn=1;n=len(a)
 for k in range(n-1):
  if a[k][k]==0:
   h=next(h for h in range(k+1,n) if a[h][k]);a[k],a[h]=a[h],a[k];sgn=-sgn
  pivot=a[k][k]
  for i in range(k+1,n):
   for j in range(k+1,n):a[i][j]=(pivot*a[i][j]-a[i][k]*a[k][j])//prev
  prev=pivot
 return sgn*a[-1][-1]
b=[]
for p in [3,5,7,11]:
 vals=[]
 for u in range(1,p):
  for v in range(1,p):
   if u==v:continue
   A=[[0]*(p-1) for _ in range(p-1)]
   for j in range(p-1):
    for x,sgn in [(v,1),(u,-1)]:
     e=(j+x)%p
     if e==p-1:
      for i in range(p-1):A[i][j]-=sgn
     else:A[e][j]+=sgn
   vals.append(det(A))
 assert set(vals)=={p};b.append(dict(p=p,ordered_distinct_automorphism_pairs=len(vals),determinants=sorted(set(vals))))
out['366108']=dict(executed=b,route='For distinct nonzero automorphisms sigma(zeta)=zeta^u,tau(zeta)=zeta^v, A represents multiplication by zeta^v-zeta^u; det A=Norm(zeta^u)*Norm(zeta^(v-u)-1)=1*Phi_p(1)=p. This short standard norm adaptation earns no credit; literal omitted distinct/nonzero hypotheses.',limit='No new theorem/novelty claim; source v3 still labels Conj3.12. No full dependency audit.')
(P/'bounded-calculations.json').write_text(json.dumps(out,indent=2)+'\n');print(json.dumps(out,indent=2))
