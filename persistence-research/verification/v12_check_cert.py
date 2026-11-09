# Parent's independent checker for GLM r7 certificates (10^L + K = 2^t0 3^a 7^w, L > t0).
import json, sys, math
K=int(sys.argv[1]); nodes=[json.loads(l) for l in open(sys.argv[2])]
t0=(K&-K).bit_length()-1
def v(x,p):
    c=0
    while x and x%p==0: x//=p; c+=1
    return c
def fac(n):
    f={}; p=2
    while p*p<=n:
        while n%p==0: f[p]=f.get(p,0)+1; n//=p
        p+=1
    if n>1: f[n]=f.get(n,0)+1
    return f
def order(g,q):
    o=q-1
    for p in fac(q-1):
        while o%p==0 and pow(g,o//p,q)==1: o//=p
    return o
def sig(r,M):
    j=v(M,3); m=3**(j+2); x=(pow(10,r,m)+K)%m
    a=(v(x,3),v(x,3)) if x else (j+2,None)
    if K%7==0: w=(0,0)
    elif M%6: w=(0,None)
    else:
        i=v(M,7); m=7**(i+1); x=(pow(10,r,m)+K)%m
        w=(v(x,7),v(x,7)) if x else (i+1,None)
    return a,w
LIFTS=[0]
def kills(q,r,M,a,w):
    d=order(10,q)
    if M%d:   # class splits mod lcm(M,d): every lift must be killed (signature recomputed at the finer modulus)
        M2=M*d//math.gcd(M,d); LIFTS[0]+=M2//M
        return all(kills(q,rr,M2,*sig(rr,M2)) for rr in range(r%M,M2,M))
    T=(pow(10,r%d,q)+K)*pow(2,-t0,q)%q
    if T==0: return True
    o3,o7=order(3,q),order(7,q); x=T
    if a[1] is not None: x=x*pow(3,-a[0],q)%q
    if w[1] is not None: x=x*pow(7,-w[0],q)%q
    if a[1] is None and w[1] is None: e=o3*o7//math.gcd(o3,o7)
    elif a[1] is None: e=o3
    elif w[1] is None: e=o7
    else: return x!=1
    return pow(x,e,q)!=1
sols=set(); nleaf=0; nrest=0; mism=0
def check(idx):
    global nleaf,nrest,mism
    nd=nodes[idx]; r,M=nd['r'],nd['m']
    if nd['k']=='l':
        nleaf+=1
        a,w=sig(r,M)
        if (list(a),list(w))!=(nd['a'],nd['w']): mism+=1
        x=nd['x']
        if 'prime' in x: assert kills(x['prime'],r,M,a,w), ("leaf not killed",nd)
        elif 'T0' in x: assert kills(x['T0'],r,M,a,w)
        elif 'sz' in x:
            assert a[1] is not None and w[1] is not None, ("size kill needs both exact",nd)
            N=2**t0*3**a[0]*7**w[0]-K
            Ls=[]
            if N>0 and str(N)=='1'+'0'*(len(str(N))-1):
                L=len(str(N))-1
                if L%M==r%M: Ls.append(L)
            sols.update(Ls)   # solutions with L > t0 in this class (child also lists small-L artifacts)
        else: raise ValueError(nd)
        return
    ch=[nodes[c] for c in nd['c']]
    Ms={c['m'] for c in ch}; assert len(Ms)==1; M2=Ms.pop(); assert M2%M==0
    lifts={r%M+k*M for k in range(M2//M)}
    chr_={c['r']%M2 for c in ch}
    assert chr_<=lifts and len(chr_)==len(ch), "children must be distinct lifts"
    for rr in lifts-chr_:
        a,w=sig(rr,M2); assert kills(nd['rest']['q'],rr,M2,a,w), ("rest lift survives",nd,rr); nrest+=1
    for c in nd['c']: check(c)
root=[i for i,n in enumerate(nodes) if n.get('p')==-1]; assert len(root)==1 and nodes[root[0]]['m']==1
check(root[0])
print(f"K={K}: leaves={nleaf} rest-lifts killed={nrest} signature mismatches={mism} lcm-lifts checked={LIFTS[0]} solutions L(>t0)={sorted(sols)}  -> CERTIFICATE VALID")
