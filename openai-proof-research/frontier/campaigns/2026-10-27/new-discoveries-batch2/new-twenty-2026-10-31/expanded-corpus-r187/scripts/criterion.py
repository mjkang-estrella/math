import pathlib,json,math
D=pathlib.Path(__file__).resolve().parents[1];hits=[];cases=0
for N in range(1,33):
 for family in ['unit_cube','all_ones']:
  for q in range(4,1001):
   if all(q%d for d in range(2,math.isqrt(q)+1)):continue
   ok=True
   for m in range(1,q//2+1):
    k=q-2*m
    b=(math.comb(m,k) if k<=m else 0) if family=='unit_cube' else math.comb(m+k-1,k)
    if pow(b,N,m):ok=False;break
   cases+=1
   if ok:hits.append({'N':N,'f':family,'composite_q':q})
 print(N,'done',len(hits),flush=True)
(D/'outputs/criterion.json').write_text(json.dumps({'cases':cases,'N':[1,32],'q':[4,1000],'families':['unit_cube','all_ones'],'hits':hits},indent=2))
