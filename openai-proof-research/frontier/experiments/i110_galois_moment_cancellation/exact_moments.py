"""Exact characteristic-two moment certificates, using cocenter projectors.
No p-adic approximation, character-table download, or writes. Run python -B.
The report proves why residue ranks recover INTEGER fixed-label counts.
"""
import json, runpy
from pathlib import Path
from math import lcm, gcd
ROOT=Path(__file__).resolve().parents[3]
D=runpy.run_path(str(ROOT/'frontier/experiments/i108_galois_tuple_divisibility/tuple_search.py'))

# Matrices over F_2 are lists of bit-packed columns.
def ident(n): return [1<<j for j in range(n)]
def mv(A,x):
    z=0
    while x:
        b=x&-x;z^=A[b.bit_length()-1];x^=b
    return z
def mm(A,B): return [mv(A,x) for x in B]
def mp(A,n):
    R=ident(len(A))
    while n:
        if n&1:R=mm(R,A)
        A=mm(A,A);n//=2
    return R
def rank(A):
    piv={}
    for x in A:
        while x:
            j=x.bit_length()-1
            if j in piv:x^=piv[j]
            else:piv[j]=x;break
    return len(piv)
def fixed_integer(P,L):
    d=rank(P)
    if not d:return 0,[]
    K=[];Ld=ident(len(L))
    for i in range(1,d+1):
        Ld=mm(L,Ld)
        K.append(d-rank([x^y for x,y in zip(mm(Ld,P),P)]))
    a={j:sum(D['old']['mu'](j//v)*K[v-1] for v in range(1,j+1) if j%v==0)//D['old']['phi'](j) for j in range(1,d+1)}
    cycles={m:sum(D['old']['mu'](j)*a[m*j] for j in range(1,d//m+1)) for m in range(1,d+1)}
    assert all(v>=0 for v in cycles.values())
    assert sum(m*v for m,v in cycles.items())==d
    assert all(sum(v*gcd(m,j) for m,v in cycles.items())==K[j-1] for j in range(1,d+1))
    return cycles[1],K

def case(name,g,a=1):
    tab,inv,orders=g;N=len(tab);ex=lcm(*orders);ep=ex
    while ep%2==0:ep//=2
    f=1
    while pow(2,f,ep)!=1%ep:f+=1
    assert gcd(a,f)==1, 'This certificate uses the fixed residue field F_2'
    t=next(v for v in range(1,ex+1) if v%(ex//ep)==1%(ex//ep) and v%ep==pow(2,a,ep))
    hs=D['old']['subgroups'](tab)
    assert not any(len(H)>1 and all(orders[x]&(orders[x]-1)==0 for x in H) and all({tab[tab[x][z]][inv[x]] for z in H}==H for x in range(N)) for H in hs)
    cs=[C for C in D['classes'](tab,inv) if orders[next(iter(C))]%2==0]
    mu=[0]*len(hs);mu[-1]=1
    for i in range(len(hs)-2,-1,-1):mu[i]=-sum(mu[j] for j in range(i+1,len(hs)) if hs[i]<hs[j])
    sums=[0]*(1<<len(cs));cert=[]
    def power(x,n):
        y=0
        for _ in range(n%orders[x]):y=tab[y][x]
        return y
    for H,u in zip(hs,mu):
        if not u:continue
        rem=set(H);hc=[]
        while rem:
            x=min(rem);C={tab[tab[y][x]][inv[y]] for y in H};hc.append(C);rem-=C
        ix={x:j for j,C in enumerate(hc) for x in C};n=len(hc)
        L=[1<<ix[power(min(C),t)] for C in hc]
        exponent=(2**f-1)*(1<<(n-1).bit_length())
        projs=[];matrices=[]
        for C in cs:
            W=[]
            for B in hc:
                x=min(B);z=0
                for y in H&C:z^=1<<ix[tab[y][x]]
                W.append(z)
            P=mp(W,exponent)
            assert mm(P,P)==P
            assert mm(P,L)==mm(L,P)
            projs.append(P);matrices.append(W)
        rows=[]
        for mask in range(1,1<<len(cs)):
            P=ident(n)
            for i,E in enumerate(projs):
                if mask>>i&1:P=mm(P,E)
            count,profile=fixed_integer(P,L)
            sums[mask]+=u*len(H)*count
            rows.append({'support_mask':mask,'fixed_labels':count,'rank_profile':profile})
        cert.append({'H':sorted(H),'mu':u,'H_classes':[sorted(C) for C in hc],
                     'class_multiplication_mod_2':matrices,'L_t':L,'projector_exponent':exponent,'projectors':projs,'fibers':rows})
    den=N//sum(all(tab[x][y]==tab[y][x] for y in range(N)) for x in range(N))
    return {'group':name,'order':N,'p':2,'a':a,'t':t,'residue_splitting_degree':f,
            'subgroups':len(hs),'singular_classes':[sorted(C) for C in cs],'D_J':den,
            'moment_numerators':sums[1:],'all_exactly_zero':all(x==0 for x in sums),
            'certificates':cert}

def main():
    cases=[('S3',D['old']['group'](3)),('A5',D['old']['group'](5,True)),
           ('D14',D['affine'](7,2)),('S3xC3',D['product'](D['old']['group'](3),3)),
           ('S3xC5',D['product'](D['old']['group'](3),5)),('S5',D['old']['group'](5))]
    rows=[case(*c) for c in cases]
    return {'method':'exact F_2 cocenter projectors and integer permutation-rank reconstruction',
            'boundary':'finite certificates only; structural justification in report','cases':rows}
if __name__=='__main__':print(json.dumps(main(),sort_keys=True))
