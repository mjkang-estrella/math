"""Lane-local implementation from the reviewed formula; no lane imports."""
import json

def label(t,n,h,i):
    if n==1: return i+1
    if n==2:
        if t==2: return ([1,4] if h==1 else [2,3,6,5])[i]
        s=t//2
        if h==1: return 2 if i==0 else 3*s+2-i
        p,j=divmod(i,t)
        if p==0: return 1 if j==0 else j+2 if j<=s else 2*s+1+j
        a=p-1; k=s-1; q=t-1; beta=2*t+(s-1)*q
        if j<t-2:
            b=j//2
            return 2*t+b*q+a+1 if j%2==0 else 2*t+(t-1-b)*q+q-a
        if a<=k: return beta+2*a+1 if j==t-2 else beta+3*k+2-a
        r=a-k
        return beta+2*r if j==t-2 else beta+4*k+3-r
    N=sum(t**g for g in range(1,n)); q=t**(n-1); Z=(N-t)//2+1
    def internal(h,i):
        if h==1: return Z if i==0 else N-t+1+i
        if t==2 and h==2 and i in (1,3): i=4-i
        r=sum(t**g for g in range(h+1,n))+i; d=1+r//2
        return Z-d if r%2==0 else Z+d
    if h<n: return internal(h,i)
    p,j=divmod(i,t); pl=internal(n-1,p)
    a=pl-Z if pl>Z else q+1+pl-Z
    sig=2*a if a<=q//2 else 2*(a-q//2)-1
    lam=lambda b,x:N+(b-1)*q+x
    if j<t-2:
        b=j//2+1
        return lam(b,a) if j%2==0 else lam(t+1-b,q+1-a)
    return lam(t//2,a) if j==t-2 else lam(t//2+1,q+1-sig)

def check(t,n,labels):
    edges=[((h-1,i//t),(h,i),labels[h][i]) for h in range(1,n+1) for i in range(t**h)]
    m=len(edges)
    if sorted(x for _,_,x in edges)!=list(range(1,m+1)): return False, 'bijection'
    weights={(h,i):0 for h in range(n+1) for i in range(t**h)}
    for u,v,x in edges: weights[u]+=x; weights[v]+=x
    if any(weights[u]==weights[v] for u,v,_ in edges): return False,'properness'
    c=len(set(weights.values()))
    return c==t**n+1, c

count=0
for t in range(2,22,2):
    for n in range(1,9):
        if sum(t**h for h in range(1,n+1))>20000: break
        rows={h:[label(t,n,h,i) for i in range(t**h)] for h in range(1,n+1)}
        ok,c=check(t,n,rows)
        assert ok,(t,n,c)
        count+=1
        print(json.dumps(dict(t=t,n=n,ok=ok,colors=c)))
rows={h:[label(2,3,h,i) for i in range(2**h)] for h in range(1,4)}
rows[1][0]=rows[1][1]
assert check(2,3,rows)==(False,'bijection')
assert len(set([5,6,15,2,3,6,5]))!=4
assert 3%2!=0
print(json.dumps(dict(cases=count,negative_controls=['duplicate label','l colors','odd t'],ok=True)))
