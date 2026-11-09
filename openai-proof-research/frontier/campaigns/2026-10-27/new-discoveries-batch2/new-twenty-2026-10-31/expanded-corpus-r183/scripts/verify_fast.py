from pathlib import Path
import json,re,math
D=Path(__file__).resolve().parents[1]
for n in [7,8]:
 s=(D/f'logs/promotion-fast{n}.log').read_text();total=int(re.search(r'total=(\d+)',s)[1]);h={int(a):int(b) for a,b in re.findall(r'orbit_size=(\d+) count=(\d+)',s)}
 nums=list(range(2,6*n+1,2));den=list(range(2,2*n+2))+list(range(4,2*n+3,2));deg=sum(nums)-sum(den);a=[0]*(deg+1);a[0]=1
 for k in nums:
  for j in range(deg,k-1,-1):a[j]-=a[j-k]
 for k in den:
  for j in range(k,deg+1):a[j]+=a[j-k]
 res=[0]*(6*n);expected=res.copy()
 for j,c in enumerate(a):res[j%(6*n)]+=c
 for sz,c in h.items():
  for j in range(sz):expected[j*6*n//sz]+=c
 assert sum(a)==total==sum(k*v for k,v in h.items()) and res==expected
 if n==7:assert h=={int(k):v for k,v in json.loads((D/'outputs/promotion-7.json').read_text())['orbits'].items()}
 r={'n':n,'linear_extensions':total,'orbits':h,'csp_residue_equal':res==expected,'method':'C lexicographic dynamic-programming rank bitset and Bender-Knuth promotion; n=7 cross-checked against Python set implementation','residues':res}
 (D/f'outputs/promotion-fast{n}.json').write_text(json.dumps(r,indent=2)+'\n');print(r)
