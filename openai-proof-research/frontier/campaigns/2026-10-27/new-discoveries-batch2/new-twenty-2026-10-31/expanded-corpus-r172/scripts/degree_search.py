import math,json,pathlib,time
D=pathlib.Path(__file__).resolve().parents[1];C=lambda n,k:math.comb(n,k) if 0<=k<=n else 0
out=[];tested=0;viol=[];positive=[]
for k in range(2,19):
 for s in range(1,9):
  threshold=(2*s+1)*k-s
  for n in sorted(set([threshold,threshold+1,threshold+2,threshold+k,2*threshold,3*threshold])):
   for r in range(1,k):
    U=C(n-r,k-r);L=U-C(n-s-r,k-r)
    base=[(C(n,r)-C(n-s,r),U),(C(n-s,r),L)]
    for j in range(2,k+1):
     m=(s+1)*j-1
     if m>n:continue
     ds=[(C(m,z)*C(n-m,r-z),sum(C(m-z,a)*C(n-m-r+z,k-r-a) for a in range(max(0,j-z),k-r+1))) for z in range(r+1) if z<=m and r-z<=n-m]
     tested+=1
     for p in (1,2,3,8):
      lhs=sum(a*b**p for a,b in ds);rhs=sum(a*b**p for a,b in base)
      if lhs>rhs:viol.append([k,s,n,r,j,p,lhs,rhs])
     # exact missing positive-part input from source
     pos=sum(a*max(0,b-L) for a,b in ds);bound=base[0][0]*(U-L)
     if pos>bound:positive.append([k,s,n,r,j,pos,bound])
     # normalize by U to avoid large-degree overflow at fractional p
     for p in (1.01,1.1,1.5,2.5):
      lhs=sum(a*(b/U)**p for a,b in ds);rhs=sum(a*(b/U)**p for a,b in base)
      if lhs>rhs*(1+1e-10):viol.append([k,s,n,r,j,p,lhs,rhs])
result={'scope':'A_j={k-sets with at least j elements of [(s+1)j-1]}; k2..18,s1..8, n in {N,N+1,N+2,N+k,2N,3N}, all 1<=r<k,2<=j<=k; N=(2s+1)k-s','family_parameter_checks':tested,'exact_p':[1,2,3,8],'floating_p':[1.01,1.1,1.5,2.5],'violations':viol,'positive_part_input_violations':positive,'limitation':'Structured competitor families only, not all matching-bounded families; fractional powers are diagnostics.'}
(D/'outputs/degree-search.json').write_text(json.dumps(result,indent=2));print(result)
