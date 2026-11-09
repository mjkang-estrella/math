#!/usr/bin/env python3
"""Fresh nd-sym verifier. Imports only the Python standard library.

PROVED soundness contract:
* Classes store L mod M and a sorted residue multiset for every coefficient.
  Sorting is the unique map from labelled positions modulo permutations of equal
  coefficients. Its fibers partition all labelled tuples (including collisions).
* A child preserves the multiplicity of EVERY parent residue. Weak compositions
  enumerate every possible distribution of that multiplicity among its lifts,
  exactly once. Every such lift is either an explicit child or independently killed.
* At an aligned prime, recompute X, the 3/7 signatures, primality and exact orders.
  At an unaligned prime, independent finite-set convolution contains all possible X
  values in the class; reject only if all are outside the necessary target coset.
* Exact signatures determine N. Enumerate all L with 10^L <= N-K and all distinct
  positions below L. Equal coefficients use increasing ACTUAL positions. Compare
  the full class-filtered solution set, not only validity of declared members.
* A separately enumerated finite brute box must match the declared size solutions.

Only scope=full proves coverage of the whole domain. scope=class is a local
positive control and is clearly reported as such. Solutions are orbit representatives;
all permutations within an equal-coefficient group follow by symmetry.
"""
import sys
sys.dont_write_bytecode=True
import argparse
import collections
import functools
import itertools
import json
import math
import pathlib


def require(b, message):
    if not b: raise ValueError(message)

@functools.lru_cache(None)
def prime(p):
    """Deterministic trial division, deliberately independent of the supply."""
    if type(p) is not int or p<2: return False
    if p%2==0: return p==2
    k=3
    while k*k<=p:
        if p%k==0: return False
        k+=2
    return True

@functools.lru_cache(None)
def factors(n):
    out=[]
    d=2
    while d*d<=n:
        if n%d==0:
            out.append(d)
            while n%d==0: n//=d
        d+=1
    if n>1: out.append(n)
    return out

@functools.lru_cache(None)
def order(b,p):
    n=p-1
    for d in factors(n):
        while n%d==0 and pow(b,n//d,p)==1: n//=d
    require(pow(b,n,p)==1,'order verification')
    return n


def val(x,p):
    require(x>0,'valuation of nonpositive integer')
    z=0
    while x%p==0: x//=p; z+=1
    return z


class Checker:
    def __init__(self,path,brute=12):
        self.powers.cache_clear()
        self.exact.cache_clear()
        records=[json.loads(s) for s in pathlib.Path(path).read_text().splitlines() if s.strip()]
        require(len(records)>1,'empty certificate')
        self.meta=records[0]
        m=self.meta
        require(m['k']=='meta' and m['format']=='nd-sym' and m['version']==1,'wrong format')
        require(m['domain']=='unordered','unsupported domain')
        require(m['scope'] in ('full','class'),'unknown scope')
        self.groups=m['groups']
        require(type(self.groups) is list,'groups type')
        require(all(type(x) is list and len(x)==2 and all(type(v) is int for v in x)
                    and x[0]>0 and x[0]%10 and x[1]>0 for x in self.groups),'bad coefficient groups')
        require([x[0] for x in self.groups]==sorted(set(x[0] for x in self.groups)),'groups not unique/sorted')
        self.coefs=tuple(c for c,n in self.groups for _ in range(n))
        require(m['dim']==len(self.coefs)+1,'dimension')
        self.K=m['K']; self.qmin=m['qmin']
        require(type(self.K) is int and self.K>0 and self.K%5,'bad constant')
        self.t=val(self.K,2)
        require(type(m.get('pin2',False)) is bool,'pin2 flag')
        self.pin2=m.get('pin2',False)
        require(type(self.qmin) is int and self.qmin>self.t,'invalid 2-adic floor')
        if self.pin2: require(self.qmin>=self.t+3,'invalid mod-8 floor')
        self.pin_digits=m.get('pin_digits',0)
        # SYM5: the domain proves any decimal depth up to qmin.
        require(type(self.pin_digits) is int and 0<=self.pin_digits<=self.qmin,'decimal pin depth')
        self.pin_representatives=[]
        self.target_cache={}
        if self.pin_digits:
            modulus=5**self.pin_digits*2**max(self.pin_digits-self.t,0)
            def cycle(base):
                seq=[1]; seen={1}  # SYM5: linear cycle membership
                v=base%modulus
                while v!=1:
                    require(v not in seen,'non-unit decimal cycle')
                    seq.append(v);seen.add(v);v=v*base%modulus
                return seq
            seq3,seq7=cycle(3),cycle(7)
            self.decimal_periods=(len(seq3),len(seq7))
            # SYM5: exact join of the same Cartesian pairs, without quadratic scanning.
            by_value=collections.defaultdict(list)
            for wr,v in enumerate(seq7): by_value[v].append(wr)
            for ar,u in enumerate(seq3):
                wanted=(self.K//2**self.t)*pow(u,-1,modulus)%modulus
                for wr in by_value[wanted]:
                    if self.pin2 and pow(3,ar,8)*pow(7,wr,8)%8!=(self.K//2**self.t)%8: continue
                    self.pin_representatives.append((ar,wr))
        self.nodes={}
        for n in records[1:]:
            require(type(n['id']) is int and n['id']>=0 and n['id'] not in self.nodes,'duplicate/bad id')
            self.nodes[n['id']]=n
        self.brute=brute
        self.stats=collections.Counter()
        self.claimed=set()
        self.root_m=m['root']['m']
        require(type(self.root_m) is int and self.root_m>0,'root modulus')
        self.root_r=self.residue(m['root']['r'],self.root_m)
        if m['scope']=='full':
            require(self.root_m==1 and self.root_r==(0,)+tuple((0,)*n for c,n in self.groups),'incomplete root')

    def residue(self,r,M):
        require(type(r) is list and len(r)==len(self.groups)+1,'residue arity')
        require(type(r[0]) is int and 0<=r[0]<M,'L residue')
        out=[r[0]]
        for xs,(c,n) in zip(r[1:],self.groups):
            require(type(xs) is list and len(xs)==n,'multiset multiplicity')
            require(all(type(x) is int and 0<=x<M for x in xs) and xs==sorted(xs),'noncanonical multiset')
            out.append(tuple(xs))
        return tuple(out)

    def key(self,pt,M):
        result=[pt[0]%M]
        off=1
        for c,n in self.groups:
            result.append(tuple(sorted(v%M for v in pt[off:off+n])))
            off+=n
        return tuple(result)

    def reduction(self,r,M):
        return (r[0]%M,)+tuple(tuple(sorted(x%M for x in xs)) for xs in r[1:])

    def distributions(self,total,slots):
        # This is a weak-composition enumeration; generator uses combinations instead.
        if slots==1:
            yield (total,)
        else:
            for first in range(total+1):
                for tail in self.distributions(total-first,slots-1): yield (first,)+tail

    def children(self,r,M,Q):
        f=Q//M
        choices=[]
        for xs in r[1:]:
            byres=collections.Counter(xs)
            partial=[()]
            for b,count in sorted(byres.items()):
                variants=[]
                for allocation in self.distributions(count,f):
                    variants.append(tuple(b+j*M for j,num in enumerate(allocation) for _ in range(num)))
                partial=[a+bv for a in partial for bv in variants]
            choices.append([tuple(sorted(a)) for a in partial])
        for ell in range(r[0],Q,M):
            for xs in itertools.product(*choices): yield (ell,)+xs

    @functools.lru_cache(None)
    def powers(self,mod,period):
        require(pow(10,period,mod)==1,'invalid decimal period')
        # Only small tables; do not allocate memory proportional to an adversarial modulus.
        if period>10000: return None
        return tuple(pow(10,e,mod) for e in range(period))

    def xmod(self,r,mod,period):
        table=self.powers(mod,period)
        def power(e): return pow(10,e%period,mod) if table is None else table[e%period]
        v=self.K+power(r[0])
        for (c,n),xs in zip(self.groups,r[1:]): v+=c*sum(power(e) for e in xs)
        return v%mod

    def signature(self,r,M):
        j=0; b=M
        while b%3==0: j+=1; b//=3
        x=self.xmod(r,3**(j+2),3**j)
        a=(j+2,False) if x==0 else (val(x,3),True)
        if M%6: return a,(0,False)
        i=0; b=M
        while b%7==0: i+=1; b//=7
        x=self.xmod(r,7**(i+1),6*7**i)
        w=(i+1,False) if x==0 else (val(x,7),True)
        return a,w

    @functools.lru_cache(None)
    def arithmetic(self,p):
        require(type(p) is int and p>7 and prime(p),'kill modulus is not prime > 7')
        return order(10,p),order(3,p),order(7,p)

    def killed(self,p,r,M):
        d,s,t=self.arithmetic(p)
        a,w=self.signature(r,M)
        if self.pin_digits:
            signature_key=(p,a[0] if a[1] else None,w[0] if w[1] else None)
            if signature_key not in self.target_cache:
                A,W=self.decimal_periods
                # Image of the free period steps in F_p^*: cyclic subgroup of
                # this order. Each decimal representative supplies one coset.
                h=math.lcm(order(pow(3,A,p),p) if not a[1] else 1,
                           order(pow(7,W,p),p) if not w[1] else 1)
                images=set()
                for ar,wr in self.pin_representatives:
                    if a[1] and a[0]%A!=ar: continue
                    if w[1] and w[0]%W!=wr: continue
                    aa=a[0] if a[1] else ar
                    ww=w[0] if w[1] else wr
                    images.add(pow(3,aa*h,p)*pow(7,ww*h,p)%p)
                self.target_cache[signature_key]=(h,images)
            h,images=self.target_cache[signature_key]
            if not images: return True
            def impossible(x): return x==0 or pow(x*pow(2,-self.t,p)%p,h,p) not in images
        else:
            alo,wlo=a[0],w[0]
            if self.pin2:
                pairs=[(i,j) for i in (0,1) for j in (0,1)
                       if pow(3,i,8)*pow(7,j,8)%8==(self.K//2**self.t)%8]
                require(len(pairs)==1,'mod-8 parity uniqueness')
                pa,pw=pairs[0]
                if (a[1] and alo%2!=pa) or (w[1] and wlo%2!=pw): return True
                if not a[1]: alo=next(v for v in (alo,alo+1) if v%2==pa)
                if not w[1]: wlo=next(v for v in (wlo,wlo+1) if v%2==pw)
                s=order(9,p);t=order(49,p)
            h=math.lcm(s if not a[1] else 1,t if not w[1] else 1)
            shift=pow(2,-self.t,p)*pow(3,-alo,p)*pow(7,-wlo,p)%p
            def impossible(x): return x==0 or pow(x*shift%p,h,p)!=1
        if M%d==0: return impossible(self.xmod(r,p,d))
        # Independent convolution; positions are labelled for this overapproximation.
        g=math.gcd(d,M)
        possible={self.K%p}
        terms=[(1,r[0])]+[(c,e) for (c,n),xs in zip(self.groups,r[1:]) for e in xs]
        for c,e in terms:
            options={c*pow(10,b,p)%p for b in range(e%g,d,g)}
            accum=set()
            for x in possible:
                for y in options: accum.add((x+y)%p)
            possible=accum
        self.stats['sumset_checks']+=1
        return all(impossible(x) for x in possible)

    def value(self,pt):
        return self.K+10**pt[0]+sum(c*10**q for c,q in zip(self.coefs,pt[1:]))

    def points(self,L):
        # Finite independent enumeration with combinations of distinct ACTUAL positions.
        def rec(g,used,seq):
            if g==len(self.groups):
                yield (L,)+seq
                return
            c,n=self.groups[g]
            available=[q for q in range(self.qmin,L) if q not in used]
            for qs in itertools.combinations(available,n):
                yield from rec(g+1,used|set(qs),seq+qs)
        yield from rec(0,set(),())

    @functools.lru_cache(None)
    def exact(self,N):
        # Exhaustive meet-in-the-middle enumeration of ALL distinct positions. This
        # shares neither recursion nor decimal decoding with generator.exact().
        R=N-self.K
        if R<=0: return ()
        out=[]
        coeffs=self.coefs
        split=len(coeffs)//2
        for L in range(self.qmin,len(str(R))):
            rem=R-10**L
            if rem<0: break
            powers=[10**q for q in range(self.qmin,L)]
            def halves(start,end):
                states=[(0,())]
                for idx in range(start,end):
                    nxt=[]
                    for value,qs in states:
                        low=qs[-1]+1 if qs and idx>start and coeffs[idx]==coeffs[idx-1] else self.qmin
                        for q in range(low,L):
                            if q in qs: continue
                            v=value+coeffs[idx]*powers[q-self.qmin]
                            if v>rem: break
                            nxt.append((v,qs+(q,)))
                    states=nxt
                return states
            left=collections.defaultdict(list)
            for v,qs in halves(0,split): left[v].append(qs)
            for v,qs in halves(split,len(coeffs)):
                for a in left.get(rem-v,()):
                    allq=a+qs
                    if len(set(allq))!=len(allq): continue
                    if any(coeffs[i]==coeffs[i+1] and allq[i]>=allq[i+1] for i in range(len(allq)-1)): continue
                    pt=(L,)+allq
                    require(self.value(pt)==N,'internal exact arithmetic')
                    out.append(pt)
        return tuple(sorted(out))

    def run(self):
        roots=[i for i,n in self.nodes.items() if n['p']==-1]
        require(len(roots)==1,'root count')
        root=roots[0]
        work=[(root,self.root_r,self.root_m)]
        seen=set()
        while work:
            i,r,M=work.pop()
            require(i not in seen,'cycle or duplicate reference')
            seen.add(i)
            nd=self.nodes[i]
            require(type(nd['m']) is int and nd['m']==M,'stored modulus mismatch')
            require(self.residue(nd['r'],M)==r,'stored residue mismatch')
            self.stats['nodes']+=1
            if nd['k']=='l':
                x=nd['x']
                if set(x)=={'prime'}:
                    require(self.killed(x['prime'],r,M),f'false prime kill at {i}')
                    self.stats['prime_leaves']+=1
                else:
                    require(set(x)=={'sz','sol'},'unknown leaf')
                    a,w=self.signature(r,M)
                    require(a[1] and w[1] and x['sz']==[a[0],w[0]],'incorrect exact signature')
                    N=2**self.t*3**a[0]*7**w[0]
                    expected=[pt for pt in self.exact(N) if self.key(pt,M)==r]
                    declared=[tuple(pt) for pt in x['sol']]
                    require(declared==sorted(set(declared)),'duplicate/noncanonical solution list')
                    require(expected==declared,f'incomplete/false size solutions at {i}')
                    self.claimed.update(expected)
                    self.stats['size_leaves']+=1
                continue
            require(nd['k']=='i','unknown node kind')
            Q=nd['m2']
            require(type(Q) is int and Q>M and Q%M==0,'invalid refinement')
            require(type(nd['c']) is list and len(set(nd['c']))==len(nd['c']),'duplicate children')
            children={}
            for j in nd['c']:
                require(j in self.nodes and self.nodes[j]['p']==i,'missing child/bad parent')
                ch=self.nodes[j]
                cr=self.residue(ch['r'],Q)
                require(ch['m']==Q and self.reduction(cr,M)==r,'child outside parent')
                require(cr not in children,'duplicate multiset class')
                children[cr]=j
                work.append((j,cr,Q))
            primes=nd['rest']
            require(type(primes) is list and all(type(p) is int for p in primes),'rest prime list')
            for cr in self.children(r,M,Q):
                self.stats['refinements']+=1
                if cr in children: continue
                for j,p in enumerate(primes):
                    if self.killed(p,cr,Q):
                        if j: primes.insert(0,primes.pop(j))
                        self.stats['rest_kills']+=1
                        break
                else: raise ValueError(f'uncovered lift at node {i}: {cr}')
        require(seen==set(self.nodes),'unreachable nodes')
        brute=[]
        for L in range(self.qmin,self.brute+1):
            for pt in self.points(L):
                if self.key(pt,self.root_m)!=self.root_r: continue
                self.stats['brute_points']+=1
                y=self.value(pt)
                require(y>0,'positive X')
                z=y
                for p in (2,3,7):
                    while z%p==0: z//=p
                if z==1 and val(y,2)==self.t:
                    brute.append(pt)
                    # Claimed membership also entails exact leaf re-verification above.
                    require(pt in self.claimed,f'brute solution omitted: {pt}')
        require(set(brute)=={pt for pt in self.claimed if pt[0]<=self.brute},'brute/claim mismatch')
        return {'label':'PROVED','result':'PASS','scope':self.meta['scope'],
                'dim':len(self.coefs)+1,'K':self.K,'groups':self.groups,'pin2':self.pin2,'pin_digits':self.pin_digits,
                'stats':dict(self.stats),'solutions':[list(pt) for pt in sorted(self.claimed)],
                'brute_Lmax':self.brute,'brute_solutions':[list(pt) for pt in brute]}


def main():
    ap=argparse.ArgumentParser(description=__doc__)
    ap.add_argument('certificate')
    ap.add_argument('brute',nargs='?',type=int,default=12)
    a=ap.parse_args()
    try:
        result=Checker(a.certificate,a.brute).run()
    except (ValueError,KeyError,TypeError,IndexError,OverflowError) as e:
        print(json.dumps({'label':'COMPUTED','result':'FAIL','error':str(e)}))
        return 1
    print(json.dumps(result))
    return 0

if __name__=='__main__': sys.exit(main())


def verify_finite_box(spec):
    """Independent finite positive-control verifier; NOT an all-L certificate.
    These boxes deliberately do not require the slice's fixed-v2 hypothesis.
    allowed_primes includes 5 only for the known five-mode controls.
    """
    K=spec['K']; qmin=spec['qmin']; B=spec['Lmax']
    coefs=tuple(spec['coefs'])
    require(list(coefs)==sorted(coefs),'box coefficient order')
    groups=sorted(collections.Counter(coefs).items())
    found=set(); count=0
    for L in range(1,B+1):
        def rec(j,used,qs):
            if j==len(groups):
                yield (L,)+qs
                return
            c,n=groups[j]
            avail=[p for p in range(qmin,L) if p not in used]
            for chunk in itertools.combinations(avail,n):
                yield from rec(j+1,used|set(chunk),qs+chunk)
        for pt in rec(0,set(),()):
            count+=1
            X=10**L+K+sum(c*10**q for c,q in zip(coefs,pt[1:]))
            y=X
            if y<=0: continue
            for p in spec['allowed_primes']:
                require(p in (2,3,5,7),'box prime set')
                while y%p==0: y//=p
            if y==1: found.add(pt)
    require(found=={tuple(pt) for pt in spec['solutions']},'finite box solution set differs')
    require(tuple(spec['required_point']) in found,'positive member not reproduced')
    require((10**spec['required_point'][0]+K+sum(c*10**q for c,q in zip(coefs,spec['required_point'][1:])))==9*spec['member'],'wrong member/configuration')
    return {'label':'COMPUTED','result':'PASS','scope':'finite-box','points':count,
            'member':spec['member'],'solutions':[list(pt) for pt in sorted(found)]}
