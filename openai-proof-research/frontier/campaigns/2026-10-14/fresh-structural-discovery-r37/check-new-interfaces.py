# Author: Myeongjin Kang (no affiliation). SPDX-License-Identifier: MIT
"""Bounded exact diagnostics, not an implementation/test of the full algorithm."""
import importlib.util,json,random
from pathlib import Path
from collections import Counter,defaultdict
HERE=Path(__file__).resolve().parent

def compute(inputs,cm,boost=True):
    rho=lambda s:''.join(cm[c] for c in s[::-1])
    req=set(inputs)|{rho(s) for s in inputs}
    req={s for s in req if s and not any(s!=t and s in t for t in req)}
    V={s[i:j] for s in req for i in range(len(s)) for j in range(i+1,len(s)+1)}
    alpha=sorted(set(''.join(req)));m={}
    def B(s,A):
        ans=0;p=len(A)
        for r in V:
            if len(r)<len(s)+2:continue
            for j in range(1,len(r)-len(s)):
                if r[j:j+len(s)]==s and all(r[h]==A[(h-j)%p] for h in range(1,len(r)-1)) and r[0]!=A[-j%p] and r[-1]!=A[(len(r)-1-j)%p]:ans+=m[r]
        return ans
    def bounds(s):
        value=max(1 if s in req else 0,sum(m.get(c+s,0) for c in alpha),sum(m.get(s+c,0) for c in alpha))
        for v in V:
            if len(v)<=len(s) or not v.startswith(s):continue
            for p in range(1,len(v)):
                if (len(v)-len(s))%p or any(v[i]!=v[i%p] for i in range(len(v))):continue
                A=v[:p];k=(len(v)-len(s))//p
                if m[v]<=B(v,A):continue
                selftext=rho(A) in (A+A)
                surplus=2*k+1 if boost and selftext else k+1
                value=max(value,B(s,A)+surplus)
        return value
    for s in sorted(V,key=lambda s:(-len(s),s)):
        if s in m:continue
        value=max(bounds(s),bounds(rho(s)))
        if s==rho(s):value+=value%2
        m[s]=m[rho(s)]=value
    return req,V,alpha,m

def check_profiles(inputs,cm,seed):
    spec=importlib.util.spec_from_file_location('historical_explore',HERE/'explore.py')
    mod=importlib.util.module_from_spec(spec);spec.loader.exec_module(mod)
    rho=lambda s:''.join(cm[c] for c in s[::-1])
    mod.rc=rho
    mod.counts=lambda inputs,fixed_boost=False:compute(inputs,cm)
    data=mod.layers(inputs,seed)
    groups=defaultdict(list)
    for layer in data['layers']:groups[layer['text']].append(layer)
    pairs=0
    for A,layers in groups.items():
        p=len(A)
        axes=[c for c in range(p) if all(cm[A[j]]==A[(c-1-j)%p] for j in range(p))]
        if not axes:continue
        assert len(layers)%2==0
        assert all(l['self_reversed'] for l in layers)
        c=axes[0]
        layers.sort(key=lambda l:tuple(l['z']))
        def z(l,x):return l['z'][x%p]+(x//p)*p
        def word(x,e):return ''.join(A[j%p] for j in range(x,e))
        def vertices(l):
            return [(x,e) for x in range(p) for e in range(z(l,x-1),z(l,x)+1)]
        def arc(l,U,V):
            x,e=U;out=[]
            while (x,e)!=V:
                if e<z(l,x):
                    e+=1;out.append(('U',word(x,e)))
                else:
                    out.append(('D',word(x,e)));x+=1
                assert len(out)<=2*p
            return out
        for lower,upper in zip(layers[::2],layers[1::2]):
            av=[v for v in vertices(upper) if (sum(v)-c)%p==0]
            assert len(av)==2,(A,av,upper)
            U,V=sorted(av,key=sum)
            assert sum(V)-sum(U)==p
            for x,e in (U,V):assert z(lower,x-1)<=e<=z(lower,x)
            W=(U[0]+p,U[1]+p)
            up1,up2=arc(upper,U,V),arc(upper,V,W)
            lo1,lo2=arc(lower,U,V),arc(lower,V,W)
            E,F=up1+lo2,lo1+up2
            mirror=lambda es:Counter(('D' if k=='U' else 'U',rho(s)) for k,s in es)
            assert len(E)==len(F)==2*p
            assert sum(k=='U' for k,s in E)==p
            assert Counter(F)==mirror(E)
            assert Counter(E+F)==Counter(up1+up2+lo1+lo2)
            pairs+=1
    return pairs

def run():
    rng=random.Random(3712803)
    maps=[{'a':'a','b':'b'},{'a':'b','b':'a'},{'a':'b','b':'a','c':'c'},{'a':'b','b':'a','c':'d','d':'c'}]
    cases=[];npairs=0
    for cm in maps:
        alpha=sorted(cm);rho=lambda s:''.join(cm[c] for c in s[::-1])
        for i in range(80):
            T=''.join(rng.choice(alpha) for _ in range(rng.randrange(1,9)))
            inputs=[]
            for _ in range(rng.randrange(1,4)):
                a=rng.randrange(len(T));b=rng.randrange(a+1,len(T)+1);s=T[a:b]
                inputs.append(rho(s) if rng.randrange(2) else s)
            req,V,active,m=compute(inputs,cm)
            occurrence=lambda text,s:sum(text[j:j+len(s)]==s for j in range(len(text)-len(s)+1))
            for s,value in m.items():
                assert value<=occurrence(T,s)+occurrence(rho(T),s)
                assert value==m[rho(s)]
                if s==rho(s):assert value%2==0
            W=sum(m[a] for a in active);assert W<=2*len(T)
            n=check_profiles(inputs,cm,i);npairs+=n
            cases.append({'cm':cm,'T':T,'inputs':inputs,'W':W,'self_pairs_checked':n})
    # A fixed positive control proving the new rule is actually exercised.
    S=['bbcbbc','bcbbcb','cbbcbb'];cm={'b':'b','c':'c'}
    old=compute(S,cm,False)[3];new=compute(S,cm,True)[3]
    assert sum(old[a] for a in cm)==6
    assert any(new[s]>old[s] for s in old)
    # An invalid count vector is rejected by the same occurrence domination predicate.
    cm={'a':'b','b':'a'};T='a';bad={'a':2,'b':2}
    wrong_count_rejected=any(value>int(s in T)+int(s in 'b') for s,value in bad.items())
    assert wrong_count_rejected
    return {'protocol':'seed3712803;80 cases per four explicit involutions; sampled feasible substrings; broad2k+1 rule without optional fixed2k+2 rule; paired transitions and actual shared-axis/spliced-edge checks','cases_checked':len(cases),'self_pairs_checked':npairs,'old_control_W':6,'new_control_W':sum(new[a] for a in ('b','c')),'wrong_count_rejected':wrong_count_rejected,'scope_limit':'bounded count domination and decomposition/splice diagnostics only; no complete connection/host/cycle/halfEuler/output implementation','cases':cases}

if __name__=='__main__':
    result=run()
    if '--write' in __import__('sys').argv:(HERE/'new-interface-checks.json').write_text(json.dumps(result,indent=2)+'\n')
    else:
        expected=json.loads((HERE/'new-interface-checks.json').read_text());assert result==expected
    print(json.dumps({k:v for k,v in result.items() if k!='cases'},sort_keys=True))
