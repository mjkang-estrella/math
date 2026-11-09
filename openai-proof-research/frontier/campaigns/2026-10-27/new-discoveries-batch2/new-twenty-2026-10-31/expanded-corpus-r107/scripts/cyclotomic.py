import pathlib,json,math
import sympy as sp
D=pathlib.Path(__file__).resolve().parents[1];out=[]
for t in range(31,62):
 for p0 in sp.factorint(2**t-1):
  p=int(p0)
  if p<=2**30 or not sp.isprime(p):continue
  H={1};u=2%p
  while u!=1:H.add(u);u=2*u%p
  H|={(-a)%p for a in list(H)};ell=(p-1)//len(H)
  if ell<3:continue
  factors=list(map(int,sp.factorint(ell)));witness=None;tested=0
  for h in sorted(H):
   if witness:break
   for k in sorted(H):
    tested+=1
    for s in sp.sqrt_mod((h*h+4*k)%p,p,all_roots=True):
     u=(h+int(s))*pow(2*k,-1,p)%p
     if u and all(pow(u,(p-1)//r,p)!=1 for r in factors):
      assert (1+h*u-k*u*u)%p==0
      witness={'u':u,'h':h,'k':k,'ell_prime_factors':factors};break
    if witness:break
  row={'p':p,'two_power_exponent':t,'subgroup_size':len(H),'ell':ell,'tested_h_k_pairs':tested,'witness_generator_coset':witness,'all_pairs_exhausted':witness is None};out.append(row);print(row,flush=True);(D/'outputs/cyclotomic.json').write_text(json.dumps(out,indent=2)+'\n')
