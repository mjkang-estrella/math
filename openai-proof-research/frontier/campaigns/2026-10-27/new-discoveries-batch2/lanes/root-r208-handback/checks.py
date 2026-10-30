"""Bounded exact controls, never a proof of Conjecture 41."""
import json

def family(m,F):
    root=frozenset(range(m,F,m))
    stack=[root]; seen=set()
    while stack:
        S=stack.pop()
        assert S not in seen
        seen.add(S)
        r=min([s for s in S if s%m]+[F+1])
        for x in range(m+1,min(r,F)):
            if x in S: continue
            if 2*x<=F and 2*x not in S:continue
            if any(x+s<=F and x+s not in S for s in S):continue
            stack.append(S|{x})
    return seen

def effective(S,m,F):
    def has(x):return x==0 or x>F or x in S
    return [x for x in range(F+1,F+m+1)
            if not any(has(a) and has(x-a) for a in range(m,x-m+1))]

def run():
    rows=[]; first_collision=None; tested=0; max_fiber=0; matching_failures=[]
    for F in range(1,27):
        for m in range(2,F+2):
            if F%m==0:continue
            ss=family(m,F); internal={s for s in ss if effective(s,m,F)}
            leaves=ss-internal
            assert len(leaves)<=len(internal)
            if 2*m>F+1:assert not leaves
            if m<F<2*m:assert len(ss)==2**(F-m-1)
            if F==m-1:assert len(ss)==1
            fibers={}
            for s in leaves:
                t=s
                while t not in internal:
                    x=min(a for a in t if a%m)
                    t=t-{x}
                    assert t in ss
                fibers.setdefault(t,[]).append(s)
            for t,ls in fibers.items():
                max_fiber=max(max_fiber,len(ls))
                if len(ls)>1 and first_collision is None:
                    first_collision=dict(m=m,F=F,target=sorted(t),leaves=[sorted(s) for s in sorted(ls,key=lambda s:tuple(sorted(s)))])
            # Test the stronger subset-injection route; no universal claim.
            adj={s:[t for t in internal if t<s] for s in leaves}
            matched={}
            def augment(s,seen):
                for t in adj[s]:
                    if t in seen:continue
                    seen.add(t)
                    if t not in matched or augment(matched[t],seen):
                        matched[t]=s;return True
                return False
            size=sum(augment(s,set()) for s in leaves)
            if size<len(leaves):matching_failures.append(dict(m=m,F=F,matched=size,leaves=len(leaves)))
            rows.append(dict(m=m,F=F,internal=len(internal),leaf=len(leaves),subset_matched=size))
            tested+=len(ss)
    # Independent exhaustive subset enumeration at small F.
    independent=0
    for F in range(1,13):
        by_m={}
        for mask in range(1<<(F-1)):
            s=frozenset(i+1 for i in range(F-1) if mask>>i&1)
            if any(a+b<=F and a+b not in s for a in s for b in s):continue
            m=min(s,default=F+1);by_m.setdefault(m,set()).add(s)
        for m in range(2,F+2):
            if F%m:assert family(m,F)==by_m.get(m,set());independent+=1
    # Source Table 5, m=4,F=14; Table 6, m=5,F=9.
    assert next(r for r in rows if r['m']==4 and r['F']==14)['internal']==5
    assert next(r for r in rows if r['m']==5 and r['F']==9)['leaf']==3
    return dict(scope='All admissible m for 1<=F<=26; finite only',semigroups=tested,pairs=len(rows),independent_pairs=independent,first_ratio_ancestor_collision=first_collision,max_ratio_ancestor_fiber=max_fiber,subset_matching_failures=matching_failures,rows=rows)

if __name__=='__main__':print(json.dumps(run(),indent=2))
