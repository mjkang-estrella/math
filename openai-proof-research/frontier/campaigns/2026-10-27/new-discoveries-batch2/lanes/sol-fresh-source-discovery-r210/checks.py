import itertools,json,hashlib
from collections import defaultdict,Counter
def edges(a):
    e=[(i,i+1) for i in range(len(a)-1)];v=len(a)
    for i,x in enumerate(a):
        for _ in range(x-1):e.append((i,v));v+=1
    return e
def dp(a,k):
    d={(c,1<<c,c):1 for c in range(k)}
    for i,x in enumerate(a):
        if i:
            z=defaultdict(int)
            for (last,m,s),v in d.items():
                for c in range(k):
                    if c!=last:z[c,m|1<<c,s+c]+=v
            d=z
        for _ in range(x-1):
            z=defaultdict(int)
            for (last,m,s),v in d.items():
                for c in range(k):
                    if c!=last:z[last,m|1<<c,s+c]+=v
            d=z
    out=Counter()
    for (_,m,s),v in d.items():out[s,m.bit_count()]+=v
    return dict(out)
def brute(a,k):
    out=Counter();e=edges(a)
    for c in itertools.product(range(k),repeat=sum(a)):
        if all(c[u]!=c[v] for u,v in e):out[sum(c),len(set(c))]+=1
    return dict(out)
def scalar(a,U):
    # Independent spine-color sum and leaf convolution, with no used-color state.
    out=Counter()
    for cs in itertools.product(U,repeat=len(a)):
        if any(cs[i]==cs[i+1] for i in range(len(a)-1)):continue
        p=Counter({sum(cs):1})
        for c,x in zip(cs,a):
            for _ in range(x-1):
                z=Counter()
                for s,v in p.items():
                    for d in U:
                        if d!=c:z[s+d]+=v
                p=z
        out.update(p)
    return out
def mobius(a,k):
    out=Counter()
    for S in range(1,1<<k):
        j=S.bit_count();U=S
        while True:
            for s,v in scalar(a,tuple(c for c in range(k) if U>>c&1)).items():out[s,j]+=(-1)**(j-U.bit_count())*v
            if U==0:break
            U=(U-1)&S
    return {x:v for x,v in out.items() if v}
def comps(n):
    if n==0:yield ();return
    for x in range(1,n+1):
        for b in comps(n-x):yield (x,)+b
def cats(n):
    # Canonical spine is precisely the set of non-leaf vertices.
    yield (n,)
    for a in comps(n-2):
        if len(a)>=2:
            a=(a[0]+1,)+a[1:-1]+(a[-1]+1,)
            if a<=a[::-1]:yield a
def signature(p):return tuple(sorted(p.items()))
def main():
    rows=[];direct=mob=0
    for n in range(3,12):
        seen={};count=0
        for a in cats(n):
            p=dp(a,4);assert p==dp(a[::-1],4)
            assert sum(p.values())==4*3**(n-1)
            if n<=7:assert p==brute(a,4);direct+=1
            if n<=8:assert p==mobius(a,4);mob+=1
            sig=signature(p);assert sig not in seen,(a,seen.get(sig));seen[sig]=a;count+=1
        rows.append({'vertices':n,'canonical_caterpillars':count,'ps4_collisions':0})
    pairs=[((2,1,3,3),(3,1,2,3)),((3,4,2,3),(4,2,3,3))]
    controls=[]
    for a,b in pairs:
        assert a!=b and a!=b[::-1] and dp(a,3)==dp(b,3)
        p,q=dp(a,4),dp(b,4);diff=sorted((s,j,p.get((s,j),0),q.get((s,j),0)) for s,j in p.keys()|q.keys() if p.get((s,j),0)!=q.get((s,j),0));assert diff
        controls.append({'a':a,'b':b,'ps3_equal':True,'first_ps4_difference':diff[0]})
    print(json.dumps({'scope':'Finite controls only, not universal proof','rows':rows,'direct_vertex_controls':direct,'mobius_controls':mob,'source_ps3_controls':controls},sort_keys=True,indent=2))
if __name__=='__main__':main()
