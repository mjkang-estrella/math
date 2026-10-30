import json,math,random,datetime,hashlib
from pathlib import Path
from functools import lru_cache
L=Path(__file__).resolve().parent
def reach(vals,M):
    steps=0
    @lru_cache(None)
    def R(mask):
        nonlocal steps
        if mask&(mask-1)==0:
            i=mask.bit_length()-1
            return {vals[i]%M:('x',i)}
        out={}; a=(mask-1)&mask; first=mask&-mask
        while a:
            b=mask^a
            if b and a&first:
                for x,ex in R(a).items():
                    for y,ey in R(b).items():
                        steps+=1
                        if steps>2000000:raise RuntimeError('two-million pair cap')
                        for v,op,left,right in [(x+y,'+',ex,ey),(x-y,'-',ex,ey),(y-x,'-',ey,ex),(x*y,'*',ex,ey)]:
                            out.setdefault(v%M,(op,left,right))
            a=(a-1)&mask
        return out
    full=(1<<len(vals))-1
    # Root-only target search; all proper subtree sets remain exact.
    for a in sorted((a for a in range(1,full) if a&1),key=lambda a:abs(2*a.bit_count()-len(vals))):
        b=full^a
        if a&1 and b:
            ra,rb=R(a),R(b)
            for x,ex in ra.items():
                for y in [(-x)%M,x]:
                    if y in rb:
                        op='+' if y==(-x)%M else '-'
                        return (op,ex,rb[y]),steps
                for y,ey in rb.items():
                    steps+=1
                    if steps>2000000:raise RuntimeError('two-million pair cap')
                    if x*y%M==0:return ('*',ex,ey),steps
    return None,steps
def evaluate(e,v):
    if e[0]=='x':return v[e[1]],[e[1]]
    a,ia=evaluate(e[1],v);b,ib=evaluate(e[2],v)
    return {'+':lambda:a+b,'-':lambda:a-b,'*':lambda:a*b}[e[0]](),ia+ib
def fmt(e,v):
    if e[0]=='x':return str(v[e[1]])
    return '('+fmt(e[1],v)+e[0]+fmt(e[2],v)+')'
rng=random.Random(155); cases=[]
pool=[a for a in range(11,400) if math.gcd(a,210)==1]
for n in [7,7,7,7]:
    v=sorted(rng.sample(pool,n));M=math.factorial(n)
    try:
        e,steps=reach(v,M)
        if e:
            value,indices=evaluate(e,v)
            assert sorted(indices)==list(range(n)) and value%M==0
            cases.append(dict(inputs=v,modulus=M,expression=fmt(e,v),value=value,pair_steps=steps,status='witness'))
        else:cases.append(dict(inputs=v,status='exact counterexample',pair_steps=steps))
    except RuntimeError as err:cases.append(dict(inputs=v,status='incomplete',error=str(err)))
# Separate-modulus choices need not combine on a common tree.
assert {3,-1,1,2}.isdisjoint({0,6,-6})
# Signed-pair induction multiplier is 2/(n-1), not an integer for n>=4.
assert 14*120==1680 and 5040%1680==0 and 1680%5040!=0
out=dict(utc=datetime.datetime.now(datetime.timezone.utc).isoformat(),cases=cases,universal_proof=False)
def restricted(v,M):
    @lru_cache(None)
    def G(mask):
        if not mask:return {1}
        i=(mask&-mask).bit_length()-1;rem=mask^(1<<i)
        ans={math.gcd(v[i]*g,M) for g in G(rem)}
        for j in range(i+1,len(v)):
            if rem>>j&1:
                for g in G(rem^(1<<j)):
                    ans.add(math.gcd((v[i]-v[j])*g,M))
                    ans.add(math.gcd((v[i]+v[j])*g,M))
        return ans
    return sorted(G((1<<len(v))-1))
for k in range(100):
    v=sorted(rng.sample(pool,7));g=restricted(v,5040)
    if 5040 not in g:
        e,steps=reach(v,5040);value,idx=evaluate(e,v)
        assert value%5040==0 and sorted(idx)==list(range(7))
        out['restricted_pairing_obstruction']=dict(inputs=v,attained_gcds=g,expression=fmt(e,v),value=value,search_index=k)
        break
out['restricted_screen']=dict(trials=k+1,found_obstruction='restricted_pairing_obstruction' in out,scope='bounded diagnostic only')
(L/'checks.json').write_text(json.dumps(out,indent=2)+'\n')
print(json.dumps(out,indent=2))
