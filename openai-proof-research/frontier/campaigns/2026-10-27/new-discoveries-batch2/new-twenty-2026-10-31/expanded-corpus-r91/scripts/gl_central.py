import pathlib,json
D=pathlib.Path(__file__).resolve().parents[1]
out=[]
for p in [3,5,7,11,13,17,19,23,29,31]:
 I=(1,0,0,1);A=(p-1,p-1,0,p-1)
 def mul(a,b):return tuple(sum(a[i*2+k]*b[k*2+j] for k in range(2))%p for i in range(2) for j in range(2))
 def power(a,n):
  b=I
  for _ in range(n):b=mul(b,a)
  return b
 def order(a):return next(i for i in range(1,2*p+1) if power(a,i)==I)
 F=[power(A,i) for i in range(p)];orders=[order(power(A,(i-j)%(2*p))) for i in range(p) for j in range(p) if i!=j]
 assert len(set(F))==p and all(o%p==0 for o in orders) and mul(F[1],F[-1]) not in F
 r=dict(p=p,generator=A,generator_order=order(A),family=F,quotient_orders=sorted(set(orders)),sylow_order=p,nonclosure_product=mul(F[1],F[-1]));out.append(r);print(p,'verified',flush=True)
(D/'outputs/gl-central.json').write_text(json.dumps(out,indent=2)+'\n')
