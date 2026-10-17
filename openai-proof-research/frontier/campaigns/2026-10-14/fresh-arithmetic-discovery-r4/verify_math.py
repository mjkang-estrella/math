"""Exact finite diagnostics; not a proof of the unrestricted theorem. MIT."""
from itertools import combinations, product
import json

def F(out,S):
    r=0
    for i,v in enumerate(out):
        if S>>i&1:r|=v
    return r

def delta(out,S):
    A=F(out,S);B=F(out,A)
    return (B&~A).bit_count()-(A&~S).bit_count()

def strongly_connected(out):
    for i in range(len(out)):
        S=1<<i
        for _ in out:S|=F(out,S)
        if S!=(1<<len(out))-1:return False
    return True

def check_boundary():
    graphs=identities=0
    for n in range(3,6):
        z=n-1;pairs=list(combinations(range(z),2))
        for cfg in product(range(3),repeat=len(pairs)):
            base=[0]*z
            for (u,v),c in zip(pairs,cfg):
                if c==1:base[u]|=1<<v
                elif c==2:base[v]|=1<<u
            for w in range(z):
                eligible=[v for v in range(z) if v!=w]
                for inc in range(1<<len(eligible)):
                    out=base[:]+[1<<w]
                    for i,v in enumerate(eligible):
                        if inc>>i&1:out[v]|=1<<z
                    graphs+=1
                    for S in range(1,1<<z):
                        A=F(base,S);B=F(base,A)
                        a=int(bool(F(out,S)>>z&1))
                        q=int(a==1 and not ((A|B)>>w&1))
                        b=int(a==0 and bool(F(out,A)>>z&1))
                        FD=F(out,S);FDD=F(out,FD)
                        assert (FDD&~FD).bit_count()==(B&~A).bit_count()+q+b
                        assert (FD&~S).bit_count()==(A&~S).bit_count()+a
                        assert delta(out,S)==delta(base,S)+q+b-a
                        if delta(out,S)<0:
                            assert delta(base,S)<=0
                            if not ((A|B)>>w&1):assert delta(base,S)<0
                        identities+=1
    return {'graphs':graphs,'nonempty_subset_identity_cases':identities}

def check_shortcut_counterexample():
    out=[36,25,10,17,37,10]
    assert strongly_connected(out)
    deficits=[delta(out,S) for S in range(1,64)]
    assert max(deficits)<=0
    singleton=[delta(out,1<<v) for v in range(6)]
    assert singleton==[0,-1,0,0,-1,0]
    witnesses={}
    for w in range(6):
        S=next(S for S in range(1,64) if delta(out,S)==0 and not ((F(out,S)|F(out,F(out,S)))>>w&1))
        witnesses[w]=S
    return {'out_bitmasks':out,'all_63_subset_deficits_nonpositive':True,
            'singleton_deficits':singleton,'unreached_zero_subset_witnesses':witnesses}

if __name__=='__main__':
    print(json.dumps({'purpose':'finite identity diagnostics, not proof or independent review',
      'boundary':check_boundary(),'invalid_shortcut_counterexample':check_shortcut_counterexample()},indent=2))
