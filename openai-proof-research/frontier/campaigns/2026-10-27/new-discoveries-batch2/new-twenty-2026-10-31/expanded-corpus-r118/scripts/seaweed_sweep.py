import sys,math,json,numpy as np
sys.path.insert(0,'scripts'); import seaweed as S
def spec_np(a,b):
    phi=S.phi_of(a,b)
    if phi is None: return None
    n=sum(a);A=np.array(S.blockid(a));B=np.array(S.blockid(b));p=np.array(phi)
    M=(A[:,None]<=A[None,:])&(B[:,None]>=B[None,:]); np.fill_diagonal(M,False)
    d=(p[:,None]-p[None,:])[M]; lo=int(d.min()); c=np.bincount(d-lo); c[-lo]+=n-1
    return [int(x) for x in c],lo
mode=sys.argv[1]; N=int(sys.argv[2]); bad=[]; cnt=0
if mode=='mp':
    for n in range(int(sys.argv[3]) if len(sys.argv)>3 else 2,N+1):
        for a in range(1,n):
            b=n-a
            if math.gcd(a,b)!=1: continue
            for (x,y) in [((a,b),(n,)),((n,),(a,b))]:
                r=spec_np(x,y); cnt+=1
                if r is None: bad.append(('notfrob',x,y)); continue
                m,lo=r
                if not S.logconcave(m) or 0 in m: bad.append((x,y,lo,m))
    print('maximal parabolic n<=',N,'cases',cnt,'failures',len(bad)); print(bad[:5])
elif mode=='stab2':
    for k in range(1,N+1):
        for r in range(1,N+1):
            n=2*k*r+1
            if n>int(sys.argv[3]): break
            a=tuple([2*k]*r+[1]); b=(n,); res=spec_np(a,b); cnt+=1
            if res is None: bad.append(('notfrob',k,r)); continue
            m,lo=res; hi=lo+len(m)-1
            want=(-2*k+1,2*k) if r%2 else (-k,k+1)
            ok=(lo,hi)==want and 0 not in m and S.unimodal(m)
            if not ok: bad.append((k,r,lo,hi,want,S.unimodal(m),m))
    print('stab2 cases',cnt,'failures',len(bad)); [print(x) for x in bad[:8]]
