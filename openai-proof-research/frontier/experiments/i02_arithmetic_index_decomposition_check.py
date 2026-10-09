# Finite sanity check of the deterministic index-divisor decomposition used in the
# bounded-index theorem (NOT evidence for the asymptotic claims).
import sys
def primerange(lo,hi):
    hi=int(hi); sv=bytearray([1])*(hi+1); sv[0:2]=b'\x00\x00'
    for i in range(2,int(hi**0.5)+1):
        if sv[i]: sv[i*i::i]=bytearray(len(sv[i*i::i]))
    return [i for i in range(max(lo,2),hi) if sv[i]]
def factorint(n):
    f={};d=2
    while d*d<=n:
        while n%d==0: f[d]=f.get(d,0)+1; n//=d
        d+=1
    if n>1: f[n]=f.get(n,0)+1
    return f
def n_order(a,p):
    o=p-1
    for q in factorint(p-1):
        while o%q==0 and pow(a,o//q,p)==1: o//=q
    return o
a=int(sys.argv[1]) if len(sys.argv)>1 else 2
x=int(sys.argv[2]) if len(sys.argv)>2 else 200000
theta=0.35; Y0=30
kq={q:(6 if q==2 else 4 if q==3 else 3) for q in primerange(2,Y0+1)}
B=1
for q,k in kq.items(): B*=q**(k-1)
stats=dict(G=0,B1=0,B2=0,B3=0,good=0,violations=0,total=0,bounded_all=0)
for p in primerange(x+1,2*x+1):
    if a%p==0: continue
    stats['total']+=1
    i=(p-1)//n_order(a,p)
    if i<=B: stats['bounded_all']+=1
    f=factorint(p-1); Q=max(f)
    if not Q> x**(1-theta): continue
    stats['G']+=1
    b1 = i%Q==0
    b2 = any(Y0<q<2*x**theta and pow(a,(p-1)//q,p)==1 for q in f if q!=Q)
    b3 = any(f.get(q,0)>=k for q,k in kq.items())
    stats['B1']+=b1; stats['B2']+=b2; stats['B3']+=b3
    if not(b1 or b2 or b3):
        stats['good']+=1
        if i>B or any(q>Y0 for q in factorint(i)): stats['violations']+=1
print("a=",a,"x=",x,"B=",B,stats)
assert stats['violations']==0
