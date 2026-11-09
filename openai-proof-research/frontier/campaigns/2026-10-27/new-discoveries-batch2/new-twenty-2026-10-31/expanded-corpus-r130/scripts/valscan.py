# Exhaustive scan for MathDB 342364 (Ulas-Zmija Conjecture 6.1).
# c_m(n): coefficients of C(x)^m, C(x)=1/(1-x) * prod_{i>=0} 1/(1-x^{2^i}) (source Section 2, C=G_2).
# Arithmetic mod 2^B (exact valuations are certified only when v < B).
import sys, json
N=int(sys.argv[1]); mlo=int(sys.argv[2]); mhi=int(sys.argv[3]); B=int(sys.argv[4]) if len(sys.argv)>4 else 64
L=4*N+1; M=(1<<B)-1
# base series C mod 2^B
a=[0]*L; a[0]=1
for n in range(1,L): a[n]=a[n-1]  # 1/(1-x)
p=1
while p<L:
    for n in range(p,L): a[n]=(a[n]+a[n-p])&M
    p*=2
W=2*B+L.bit_length()+2
def pack(c): return int.from_bytes(b''.join(x.to_bytes(W//8+1,'little') for x in c),'little') if False else sum(x<<(W*i) for i,x in enumerate(c))
def pack2(c):
    bs=(W+7)//8
    return int.from_bytes(b''.join(x.to_bytes(bs,'little') for x in c),'little'), bs
def unpack(z,bs):
    by=z.to_bytes((z.bit_length()+7)//8+bs,'little')
    return [int.from_bytes(by[i*bs:(i+1)*bs],'little')&M for i in range(L)]
Ap,bs=pack2(a)
def v2(x): return (x&-x).bit_length()-1 if x else None
cur=[1]+[0]*(L-1)
for m in range(1,mhi+1):
    z,_=pack2(cur); cur=unpack(z*Ap,bs)
    if m<mlo: continue
    if m%2==0:
        k=m//2; base=2*v2(k)+3; kind='even'
    else:
        base=3 if m%4==1 else 6; kind='1mod4' if m%4==1 else '3mod4'
    hist={}; bad=[]; firstmin=None; unknown=0
    for n in range(1,N+1):
        d=(cur[4*n]-cur[n])&M; v=v2(d); goal=v2(n)+base
        if v is None: unknown+=1; continue
        e=v-goal; hist[e]=hist.get(e,0)+1
        if (kind=='even' and e!=0) or (kind!='even' and e<0): bad.append([n,v,goal])
    mn=min(hist) if hist else None
    eq=[n for n in range(1,N+1) if (lambda d:(d!=0 and v2(d)==v2(n)+base))((cur[4*n]-cur[n])&M)][:8]
    print(json.dumps(dict(m=m,kind=kind,N=N,bits=B,min_excess=mn,equality_first_n=eq,bad_count=len(bad),bad_first=bad[:5],undetermined_mod_2B=unknown,hist=dict(sorted(hist.items())))),flush=True)
