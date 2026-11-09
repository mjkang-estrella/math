import sys,json
from functools import lru_cache
from collections import Counter
def cop(w): return [(w[:i],w[i+1:]) for i in range(len(w))]
@lru_cache(None)
def Mrs(r,s,n,u,v):
    out=Counter()
    if n<2: return out
    if n==2:
        if (r,s)==(1,2): out[u+'a'+v]+=1
        elif (r,s)==(2,1): out[v+'b'+u]+=1
        return out
    if r==1:
        for u1,u2 in cop(u):
            for w,c in Mrs(2,s,n-1,u2,v).items(): out[u1+'a'+w]+=c
    else:
        for v1,v2 in cop(v):
            for w,c in Mrs(1,s,n-1,u,v2).items(): out[v1+'b'+w]+=c
    return out
def M(u,v):
    out=Counter()
    for r in (1,2):
        for s in (1,2):
            for n in range(2,len(u)+len(v)+3):
                if (n-r-s-1)%2==0:
                    for w,c in Mrs(r,s,n,u,v).items(): out[w]+=c
    return out
def I2w(w):
    out=Counter({w:1}); out[w[::-1]]+=1
    for u1,u2 in cop(w):
        for x,c in M(u1[::-1],u2).items(): out[x]+=c
    return out
U="aaaba + aaabb - 2aabaa - aabba + aabbb + abaaa + abaab - abbaa + abbab - 2abbba - 2baaab + baaba - baabb + babba + babbb + bbaaa - bbaab - 2bbabb + bbbaa + bbbab"
u=Counter(); sign=1
for tok in U.replace('- ','-').replace('+ ','+').split():
    t=tok; sg=1
    if t[0] in '+-': sg=-1 if t[0]=='-' else 1; t=t[1:]
    c=1
    if t[0].isdigit(): c=int(t[0]); t=t[1:]
    u[t]+=sg*c
assert len(u)==20 and all(len(w)==5 for w in u)
sym=all(u[w]==u[w[::-1]] for w in u)
img=Counter()
for w,c in u.items():
    for x,d in I2w(w).items(): img[x]+=c*d
zero=all(v==0 for v in img.values())
# kernel dims via rational rank for n=1..6
from fractions import Fraction
import itertools
def rank(rows):
    rows=[r[:] for r in rows]; rk=0; ncol=len(rows[0]) if rows else 0
    for c in range(ncol):
        piv=next((i for i in range(rk,len(rows)) if rows[i][c]!=0),None)
        if piv is None: continue
        rows[rk],rows[piv]=rows[piv],rows[rk]
        for i in range(len(rows)):
            if i!=rk and rows[i][c]!=0:
                f=Fraction(rows[i][c],rows[rk][c]); rows[i]=[a-f*b for a,b in zip(rows[i],rows[rk])]
        rk+=1
    return rk
dims={}
for n in range(1,7):
    W=[''.join(p) for p in itertools.product('ab',repeat=n)]
    idx={w:i for i,w in enumerate(W)}
    cols=[]
    for w in W:
        im=I2w(w); cols.append([im.get(x,0) for x in W])
    r=rank(cols); fixed=sum(1 for w in W if w==w[::-1])
    dims[n]={'ker':len(W)-r,'A':(len(W)-fixed)//2}
# ER check M(a,1)
out={'u_symmetric':sym,'I2_u_zero':zero,'u_nonzero':True,'M_a_1':dict(M('a','')),'dims':dims}
print(json.dumps(out)); json.dump(out,open(sys.argv[1],'w'),indent=1)
