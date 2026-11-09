# Genus ranges of chord diagrams (329080; Cahoon et al., arXiv:1410.6148, Def. 2.1).
# Ribbon-graph model: backbone = cycle on the 2n endpoints, each endpoint has rotation
# (N,P,C) if the band end is inside and (N,C,P) if outside; faces = cycles of rho o theta,
# genus g = (2 + n - f)/2 (source Lemma 3.1).
import sys,itertools,json,time
def canon(w):
    n=len(w); best=None
    for v in (w,w[::-1]):
        for s in range(n):
            u=v[s:]+v[:s]; m={}; out=[]
            for c in u:
                if c not in m: m[c]=len(m)
                out.append(m[c])
            t=tuple(out)
            if best is None or t<best: best=t
    return best
def prep(w):
    L=len(w); partner=[0]*L; seen={}
    for i,c in enumerate(w):
        if c in seen: partner[i]=seen[c]; partner[seen[c]]=i
        else: seen[c]=i
    theta=[0]*(3*L)
    for i in range(L):
        j=(i+1)%L; theta[3*i]=3*j+1; theta[3*j+1]=3*i
        theta[3*i+2]=3*partner[i]+2
    return theta
def faces(theta,L,mask):
    # mask bit i = 1 -> endpoint i outside
    rho=[0]*(3*L)
    for i in range(L):
        N,P,C=3*i,3*i+1,3*i+2
        if (mask>>i)&1: rho[N]=C;rho[C]=P;rho[P]=N
        else: rho[N]=P;rho[P]=C;rho[C]=N
    seen=bytearray(3*L); f=0
    for h in range(3*L):
        if not seen[h]:
            f+=1; x=h
            while not seen[x]:
                seen[x]=1; x=rho[theta[x]]
    return f
def genus_range(w,stop_max=None):
    L=len(w); n=L//2; theta=prep(w); gs=set()
    # global in/out swap is a mirror: fix bit 0 = 0
    for mask in range(0,1<<L,2):
        f=faces(theta,L,mask); g=(2+n-f)//2; gs.add(g)
        if stop_max is not None and g>stop_max: return gs,False
    return gs,True
if __name__=='__main__':
    for w in ['11','1212','1122','123123','123132','123321','12312345674675']:
        t=tuple(int(c) for c in w); print(w,sorted(genus_range(t)[0]))
