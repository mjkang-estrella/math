# Closed forms of Lemmas L1-L5 (see REPORT.md); directions 1=IN, 2=OUT, 0=F (free)
IN,OUT,F=1,2,0
def inS(b,m): return (b & (m-1))==0
def L1(k,a,i,b):            # Gamma(I;(k,a),(i,b)), a,b blocked
    if (k,a)==(1,OUT): return i^1
    if (i,b)==(1,OUT): return k^1
    return (k+i+(a==b))%2
def L2(i,b):                # Gamma(I;(1,F),(i,b))
    if b==F: return (i+1)%2
    if b==IN: return i-1 if i%4==3 else i+1
    return i-1 if i%4==1 else i+1
def L3(y,i,b):              # Gamma(I;(y,F),(i,b)), y even >=4
    if i==1: return y+1 if b==IN else 1
    return y-2+((i+(b==IN))%2)
def L4(k,a,i,b):            # Gamma(N;(1,F),(k,a),(i,b))
    if k==1 and i==1 and a==b: return 3
    return (k+i+(a!=b))%2
def eps(i,m):
    if i%2==1: return -1 if inS((i-1)//2,m) else 0
    return 1 if inS(i//2,m) else 0
def L5(y,i):                # Gamma(N;(1,F),(y,F),(i,delta)), y=2m>=4, any delta
    m=y//2
    return i+y-2+eps(i,m)
def flip(d): return {IN:OUT,OUT:IN,F:F}[d]
def gform(y,z):             # Theorem: g(S(1,2m,z))
    m=y//2; n=z-y+2; b,r=divmod(n,4)
    if inS(b,m): return 1 if r==2 else 0
    return z%2
