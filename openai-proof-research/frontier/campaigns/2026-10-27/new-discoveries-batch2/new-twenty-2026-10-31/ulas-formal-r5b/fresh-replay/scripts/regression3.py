"""Independent exact regression of the NEW reducedTerm definition, not a proof of Lemma R."""
from math import comb

def choose(n,k): return comb(n,k) if k<=n else 0

def reduced(m,R):
    out={}
    for E,a in enumerate(R):
        for i in range(m+E//2+2):
            F=E//2+i; b=2*i+(1 if E%2==0 else 0)
            out[F]=out.get(F,0)+a*2**b*choose(m+E//2+i+1,b)
    return out

def series_y(R,L):
    out=[0]*L; out[0]=R[0] if R else 0
    for E in range(1,len(R)):
        for n in range(E,L): out[n]+=R[E]*choose(n-1,E-1)
    return out

def mul(a,b,L):
    return [sum(a[i]*b[n-i] for i in range(n+1)) for n in range(L)]

def Cpow(m,L):
    f=[1]+[0]*(L-1)
    for _ in range(m):
        for s in [1]+[2**i for i in range(L.bit_length()) if 2**i<L]:
            for n in range(s,L): f[n]+=f[n-s]
    return f

pairs=0
for m in range(13):
    for E in range(10):
        R=[0]*E+[1]; red=reduced(m,R)
        assert red.get(0,0)==(2*(m+1) if E==0 else 1 if E==1 else 0)
        for F,a in red.items():
            if not a: continue
            gain=(abs(a)&-abs(a)).bit_length()-1+E.bit_length()-F.bit_length()
            assert gain>=1
            if not (F==E//2 and (E==0 or E%2==1)): assert gain>=2
        L=32; q=[0]+R[:]
        q.append(0)
        for i,a in enumerate(R): q[i+2]+=a
        p=[red.get(i,0) for i in range(max(red)+1)]
        r=[0]+p[:];r.append(0)
        for i,a in enumerate(p): r[i+2]+=a
        lhs=mul(Cpow(m,2*L),series_y(q,2*L),2*L)[::2]
        rhs=mul(Cpow(m,L),series_y(r,L),L)
        assert lhs==rhs,(m,E)
        pairs+=1
print('Reduced operator regression passed:',pairs,'monomials, 32 coefficients; gains and constants passed.')
