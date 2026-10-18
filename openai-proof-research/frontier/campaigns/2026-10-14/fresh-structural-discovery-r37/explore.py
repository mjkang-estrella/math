# Author: Myeongjin Kang. No affiliation. SPDX-License-Identifier: MIT
"""Exact exploratory symmetric counts, paired walks, and sorted profiles."""
import itertools as it
from collections import Counter,defaultdict
import random,json

def rc(s):return s[::-1]
def counts(inputs, fixed_boost=False):
    req=set(inputs)|{rc(s) for s in inputs}
    req={s for s in req if s and not any(s!=t and s in t for t in req)}
    V={s[i:j] for s in req for i in range(len(s)) for j in range(i+1,len(s)+1)}
    alpha=sorted(set(''.join(req))); m={}
    def B(s,p):
        total=0
        for r in V:
            if len(r)<len(s)+2:continue
            for j in range(1,len(r)-len(s)):
                if r[j:j+len(s)]==s and all(r[h]==p[(h-j)%len(p)] for h in range(1,len(r)-1)) and r[0]!=p[-j%len(p)] and r[-1]!=p[(len(r)-1-j)%len(p)]:total+=m[r]
        return total
    def bound(s):
        lower=[int(s in req),sum(m.get(c+s,0) for c in alpha),sum(m.get(s+c,0) for c in alpha)]
        for v in V:
            if len(v)<=len(s) or not v.startswith(s):continue
            for p in range(1,len(v)):
                if (len(v)-len(s))%p or not all(v[h]==v[h%p] for h in range(len(v))):continue
                if m[v]>B(v,v[:p]):lower.append(B(s,v[:p]) + (2 if fixed_boost and v==rc(v) else 1)*((len(v)-len(s))//p+1))
        return max(lower)
    for s in sorted(V,key=lambda s:(-len(s),s)):
        if s in m:continue
        v=max(bound(s),bound(rc(s)))
        if s==rc(s):v+=v%2
        m[s]=m[rc(s)]=v
    return req,V,alpha,m

def layers(inputs,seed=0,fixed_boost=False):
    req,V,alpha,m=counts(inputs, fixed_boost=fixed_boost)
    edges=[];tau={};out=defaultdict(list);inc=defaultdict(list)
    for s in sorted(V):
        u=m[s]-sum(m.get(c+s,0) for c in alpha)
        # Every up copy is paired to a down copy at rc(s).
        for k in range(u):
            a=len(edges);b=a+1;t=rc(s)
            edges.extend([(s[:-1],s,'U',s),(t,t[1:],'D',t)])
            tau[a]=b;tau[b]=a
    for i,(a,b,_,_) in enumerate(edges):out[a].append(i);inc[b].append(i)
    rng=random.Random(seed);succ={};done=set()
    for v in sorted(set(out)|set(inc)):
        if v in done:continue
        w=rc(v);done.update((v,w))
        assert len(out[v])==len(inc[v])
        if v==w:
            os=out[v][:];rng.shuffle(os);assert len(os)%2==0
            for a,b in zip(os[::2],os[1::2]):succ[tau[a]]=b;succ[tau[b]]=a
        else:
            ins=inc[v][:];os=out[v][:];rng.shuffle(os)
            for a,b in zip(ins,os):succ[a]=b;succ[tau[b]]=tau[a]
    cycles=[];seen=set()
    for i in range(len(edges)):
        if i in seen:continue
        cyc=[];j=i
        while j not in seen:seen.add(j);cyc.append(j);j=succ[j]
        assert j==i
        cycles.append(cyc)
    cs={frozenset(c) for c in cycles}
    assert all(frozenset(tau[e] for e in c) in cs and frozenset(tau[e] for e in c)!=frozenset(c) for c in cycles)
    groups=defaultdict(lambda:defaultdict(list))
    for cyc in cycles:
        P=sum(edges[e][2]=='U' for e in cyc);assert P>0
        A=[None]*P;x=0;end=len(edges[cyc[0]][0]);downs=[]
        for ei in cyc:
            a,b,kind,s=edges[ei];assert end-x==len(a)
            if kind=='U':A[end%P]=s[-1];end+=1
            else:downs.append((x,end));x+=1
        A=''.join(A);p=next(p for p in range(1,P+1) if P%p==0 and all(A[j]==A[j%p] for j in range(P)))
        A=A[:p];canonical,k=min((A[k:]+A[:k],k) for k in range(p))
        for x,e in downs:
            r=(x-k)%p;groups[canonical][r].append(r+e-x)
    result=[]
    for A,by in groups.items():
        p=len(A);assert set(by)==set(range(p));h=len(by[0]);assert all(len(v)==h for v in by.values())
        by={r:sorted(v) for r,v in by.items()}
        for i in range(h):
            z=[by[r][i] for r in range(p)];es=Counter()
            word=lambda a,b:''.join(A[j%p] for j in range(a,b))
            for r in range(p):
                entering=z[r-1] if r else z[-1]-p
                assert r<=entering<=z[r]
                for end in range(entering+1,z[r]+1):es['U',word(r,end)]+=1
                es['D',word(r,z[r])]+=1
            mirror=Counter({('D' if kind=='U' else 'U',rc(s)):n for (kind,s),n in es.items()})
            result.append(dict(text=A,z=z,self_reversed=es==mirror,rooted=any(s=='' or (kind=='U' and len(s)==1) or (kind=='D' and len(s)==1) for (kind,s) in es),edges=sorted((k,s,n) for (k,s),n in es.items())))
    multiplicities=Counter((r['text'],tuple(r['z'])) for r in result)
    bad=[r for r in result if r['self_reversed'] and multiplicities[r['text'],tuple(r['z'])]%2]
    return dict(inputs=inputs,seed=seed,counts=m,layers=result,odd_fixed_profiles=bad)

if __name__=='__main__':
    rng=random.Random(37128)
    for trial in range(1500):
        ss=[''.join(rng.choice('abc') for _ in range(rng.randrange(2,10))) for _ in range(rng.randrange(1,5))]
        d=layers(ss,trial)
        if d['odd_fixed_profiles']:
            print(json.dumps(dict(trial=trial,**d),indent=2));break
    else:print('none in bounded search')
