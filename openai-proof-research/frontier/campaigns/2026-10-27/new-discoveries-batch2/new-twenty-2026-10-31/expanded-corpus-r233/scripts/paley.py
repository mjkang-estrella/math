import json,pathlib,math,sys,time
P=pathlib.Path(__file__).resolve().parents[1]; out=[];start=time.monotonic()
def prime(n):return n>1 and all(n%d for d in range(2,math.isqrt(n)+1))
for q in range(503,int(sys.argv[1])+1,2):
 if not prime(q):continue
 delta=next(d for d in range(2,q) if pow(d,(q-1)//2,q)==q-1)
 def mul(z,w):return ((z[0]*w[0]+delta*z[1]*w[1])%q,(z[0]*w[1]+z[1]*w[0])%q)
 def power(z,n):
  r=(1,0)
  while n:
   if n&1:r=mul(r,z)
   z=mul(z,z);n//=2
  return r
 for m in range(3,(q+1)//2+1):
  if (q+1)//2%m or m>(q+1)//3:continue
  size=(q+1)//m+1
  if size>40:continue
  exp=(q*q-1)//m
  S=[a for a in range(q) if power((a,1),exp)==(1,0)]
  C=S # -S=S since trace-zero conjugation, but verify below
  assert len(C)==(q+1)//m-1
  assert set(S)=={(-a)%q for a in S}
  allbits=(1<<q)-1;ext=[]
  for b in range(1,q):
   mask=sum(1<<((b*a)%q) for a in S)
   candidates=allbits
   for c in C:
    candidates &= ((mask<<c)|(mask>>(q-c)))&allbits
    if not candidates:break
   while candidates:
    low=candidates&-candidates;a=low.bit_length()-1;candidates-=low
    if a==0 and b in (1,q-1):continue
    if power((a,(b-1)%q),exp)==(1,0) and power((a,(b+1)%q),exp)==(1,0):ext.append([a,b])
  row={'q':q,'m':m,'delta':delta,'clique_size':size,'extensions':ext,'gcd_qminus1_mminus2':math.gcd(q-1,m-2)};out.append(row)
  print(json.dumps(row),flush=True)
  if ext:
   (P/'inputs/paley-witness.json').write_text(json.dumps({'row':row,'real_clique':C},indent=2));raise SystemExit('WITNESS diagnostic only')
(P/'inputs/paley-search.json').write_text(json.dumps({'parameters':out,'complete_range':[503,int(sys.argv[1])],'restriction':'q prime; m>=3 divides (q+1)/2; m<=(q+1)/3; clique size<=40; one alpha with alpha^2=least quadratic nonresidue; all q^2 possible extension vertices checked by bitset intersection','seconds':time.monotonic()-start},indent=2))
