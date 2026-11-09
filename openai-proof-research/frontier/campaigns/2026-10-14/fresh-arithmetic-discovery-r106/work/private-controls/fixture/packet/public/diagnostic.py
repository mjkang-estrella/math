"""Finite rational centralizer checks only; MIT. No proof or division test."""
from fractions import Fraction as F
import json

def qmul(i,j):
    # Hamilton multiplication; basis 1,i,j,k.
    if i==0:return (1,j)
    if j==0:return (1,i)
    if i==j:return (-1,0)
    tab={(1,2):(1,3),(2,3):(1,1),(3,1):(1,2)}
    if (i,j) in tab:return tab[i,j]
    s,k=tab[j,i];return (-s,k)
def mul(i,j,tensor):
    if not tensor:return qmul(i,j)
    a,b=divmod(i,4);c,d=divmod(j,4)
    s,e=qmul(a,c);t,f=qmul(b,d)
    return s*t,4*e+f
def rank(a):
    a=[[F(x) for x in r] for r in a];r=0
    for c in range(len(a[0])):
        pivot=next((j for j in range(r,len(a)) if a[j][c]),None)
        if pivot is None:continue
        a[r],a[pivot]=a[pivot],a[r];v=a[r][c];a[r]=[x/v for x in a[r]]
        for j in range(r+1,len(a)):
            if a[j][c]:
                v=a[j][c];a[j]=[x-v*y for x,y in zip(a[j],a[r])]
        r+=1
        if r==len(a):break
    return r
def dimension(n,pencils,tensor=False):
    dim=16 if tensor else 4
    mons=[(i,j) for i in range(n) for j in range(i,n)]
    rows=[]
    for p in pencils:
        a=[[0]*(dim*n) for _ in range(len(mons)*dim)]
        for i in range(n):
            for b in range(dim):
                for j,c,v in p:
                    m=mons.index(tuple(sorted((i,j))))
                    s,k=mul(b,c,tensor);a[m*dim+k][i*dim+b]+=v*s
                    s,k=mul(c,b,tensor);a[m*dim+k][i*dim+b]-=v*s
        rows.extend(a)
    return dim*n-rank(rows)
def main():
    out={}
    for n in (2,3,4,5):
        got=dimension(n,[[(0,1,1),(1,2,1)]])
        assert got==n+1;out['quaternion_rank2_n'+str(n)]=got
    assert dimension(3,[[(0,1,1),(1,2,1),(2,3,1)]])==4
    assert dimension(3,[[(0,1,1)]])==6
    assert dimension(3,[[(0,0,1)]])==12
    out.update(rank3=4,rank1_control=6,scalar_control=12)
    u=[(0,4,1),(1,8,1)];v=[(1,1,1),(2,2,1)]
    got=dimension(3,[u,v],True);assert got==5;out['separated_tensor_n3']=got
    out['scope']='8 finite centralizer dimensions; tensor Hamilton algebra is split, not a division witness'
    print(json.dumps(out,indent=2,sort_keys=True))
if __name__=='__main__':main()
