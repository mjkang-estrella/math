import math,json,pathlib
O=pathlib.Path(__file__).resolve().parent
def deg(x):return x.bit_length()-1
def rem(a,b):
 while a and deg(a)>=deg(b):a^=b<<(deg(a)-deg(b))
 return a
def mul(a,b):
 c=0
 while b:
  if b&1:c^=a
  b>>=1;a<<=1
 return c
def factors(a):
 ds=[]
 for d in range(1,deg(a)+1):
  for b in range((1<<d)|1,1<<(d+1),2):
   if rem(a,b)==0:
    ds.append(d)
    while rem(a,b)==0:
     q=0;r=a
     while r and deg(r)>=d:
      k=deg(r)-d;q^=1<<k;r^=b<<k
     a=q
 return ds
def lam(s,r):
 a=mul(s,r);out=0
 for j in range(0,deg(a)+1,2):
  if a>>j&1:out^=1<<(j//2)
 return out
def rank(cols):
 piv={}
 for a in cols:
  while a:
   k=deg(a)
   if k in piv:a^=piv[k]
   else:piv[k]=a;break
 return len(piv)
rows=[]
for d in range(1,7):
 for r in range((1<<d)|1,1<<(d+1),2):
  ds=factors(r);ell=math.lcm(*ds)
  for m in range(1,ell+1):
   if ell%m:continue
   cols=[]
   for j in range(d+1):
    s=1<<j
    for _ in range(m):s=lam(s,r)
    cols.append(s^(1<<j))
   dim=d+1-rank(cols);pred=1+sum(math.gcd(m,a) for a in ds)
   rows.append({'R_binary':r,'degree':d,'irreducible_degrees_distinct':ds,'m':m,'dimension':dim,'predicted':pred})
out={'scope':'Executed exact GF(2) polynomial/matrix arithmetic, every monic constant-one R of degree 1 through 6 and every permitted divisor m. Parameter evidence only; not full q or degree proof.','polynomials':63,'cases':len(rows),'mismatches':[x for x in rows if x['dimension']!=x['predicted']],'rows':rows}
(O/'dimension-probe.json').write_text(json.dumps(out,indent=2)+'\n');print({k:v for k,v in out.items() if k!='rows'})
