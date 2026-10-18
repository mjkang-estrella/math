"""Finite exact diagnostics only; no proof or review verdict. Standard library."""
import itertools, json
from collections import deque

class Field:
    def __init__(self,p,d):
        self.p,self.d,self.q=p,d,p**d
        def rem(a,b):
            a=a[:]
            while a and a[-1]==0:a.pop()
            while len(a)>=len(b):
                c=a[-1]; k=len(a)-len(b)
                for j,v in enumerate(b):a[k+j]=(a[k+j]-c*v)%p
                while a and a[-1]==0:a.pop()
            return a
        for c in itertools.product(range(p),repeat=d):
            if not c[0]:continue
            f=list(c)+[1]
            if all(rem(f,list(b)+[1]) for k in range(1,d//2+1) for b in itertools.product(range(p),repeat=k)):
                self.f=f;break
        self.v=[tuple((x//p**i)%p for i in range(d)) for x in range(self.q)]
    def enc(self,a):return sum(v*self.p**i for i,v in enumerate(a))
    def add(self,a,b):return self.enc([(x+y)%self.p for x,y in zip(self.v[a],self.v[b])])
    def neg(self,a):return self.enc([(-x)%self.p for x in self.v[a]])
    def scale(self,a,c):return self.enc([(x*c)%self.p for x in self.v[a]])
    def mul(self,a,b):
        c=[0]*(2*self.d-1)
        for i,x in enumerate(self.v[a]):
            for j,y in enumerate(self.v[b]):c[i+j]=(c[i+j]+x*y)%self.p
        for k in range(len(c)-1,self.d-1,-1):
            for j in range(self.d):c[k-self.d+j]=(c[k-self.d+j]-c[k]*self.f[j])%self.p
        return self.enc(c[:self.d])
    def power(self,a,n):
        r=1
        while n:
            if n%2:r=self.mul(r,a)
            a=self.mul(a,a);n//=2
        return r
    def beta(self,a,b):return self.add(self.mul(a,self.power(b,self.p)),self.neg(self.mul(self.power(a,self.p),b)))
    def tr(self,a):
        r=0
        for _ in range(self.d):r=self.add(r,a);a=self.power(a,self.p)
        assert all(x==0 for x in self.v[r][1:])
        return self.v[r][0]

def rank(a,p):
    a=[r[:] for r in a];r=0
    for j in range(len(a[0])):
        k=next((k for k in range(r,len(a)) if a[k][j]%p),None)
        if k is None:continue
        a[r],a[k]=a[k],a[r];iv=pow(a[r][j],-1,p);a[r]=[(x*iv)%p for x in a[r]]
        for k in range(len(a)):
            if k!=r:
                c=a[k][j];a[k]=[(x-c*y)%p for x,y in zip(a[k],a[r])]
        r+=1
    return r

def form_checks(p,d):
    F=Field(p,d);basis=[p**i for i in range(d)];hist={}
    for a in range(1,F.q):
        M=[[F.tr(F.mul(a,F.beta(x,y))) for y in basis] for x in basis]
        r=rank(M,p);assert r==d-1;hist[str(r)]=hist.get(str(r),0)+1
        roots=sum(F.power(x,p*p)==F.mul(F.power(a,(1-p)%(F.q-1)),x) for x in range(F.q))
        assert roots==p
    return {'p':p,'d':d,'polynomial':F.f,'nonzero_form_rank_histogram':hist,'all_radical_sizes':p}

def small_group():
    F=Field(3,3);p=3;d=3;q=27;mod=9;N=729
    vec=[tuple((x//mod**i)%mod for i in range(d)) for x in range(N)]
    enc=lambda a:sum(v*mod**i for i,v in enumerate(a))
    bar=[F.enc([v%p for v in a]) for a in vec]
    cent=[enc([p*v for v in a]) for a in F.v]
    bt=[[F.beta(a,b) for b in range(q)] for a in range(q)]
    def mul(x,y):
        c=F.v[bt[bar[x]][bar[y]]]
        return enc([(a+b+p*2*z)%mod for a,b,z in zip(vec[x],vec[y],c)])
    # All two-variable power/commutator interfaces; associativity on all basis triples.
    for x in range(N):
        r=0
        for _ in range(p):r=mul(r,x)
        assert r==cent[bar[x]]
        for y in range(N):
            assert mul(x,y)==mul(mul(y,x),cent[bt[bar[x]][bar[y]]])
    test=[0]+[mod**i for i in range(d)]+[cent[p**i] for i in range(d)]
    for x,y,z in itertools.product(test,repeat=3):assert mul(mul(x,y),z)==mul(x,mul(y,z))
    def extend(S,v):return frozenset(F.add(x,F.scale(v,c)) for x in S for c in range(p))
    spaces={frozenset([0])};queue=list(spaces)
    for S in queue:
        for v in range(q):
            T=extend(S,v)
            if T not in spaces:spaces.add(T);queue.append(T)
    spaces=sorted(spaces,key=lambda s:(len(s),tuple(sorted(s))))
    def basis(S):
        out=[];span=frozenset([0])
        for v in sorted(S):
            if v not in span:out.append(v);span=extend(span,v)
        return out
    def closure(gens):
        S={0};queue=deque([0])
        while queue:
            x=queue.popleft()
            for g in gens:
                y=mul(x,g)
                if y not in S:S.add(y);queue.append(y)
        return frozenset(S)
    subs={}
    # Every subgroup is represented by U⊂W, beta(U,U)⊂W and lifts of a basis of U modulo W.
    for U in spaces:
        ub=basis(U)
        for W in spaces:
            if not U<=W or any(bt[x][y] not in W for x in ub for y in ub):continue
            reps=[];covered=set()
            for v in range(q):
                if v not in covered:
                    reps.append(v);covered.update(F.add(v,w) for w in W)
            for shifts in itertools.product(reps,repeat=len(ub)):
                gens=[cent[w] for w in basis(W)]
                gens += [enc([(a+p*b)%mod for a,b in zip(F.v[u],F.v[t])]) for u,t in zip(ub,shifts)]
                H=closure(gens)
                assert len(H)==len(U)*len(W)
                assert {bar[x] for x in H}==set(U)
                assert {v for v in range(q) if cent[v] in H}==set(W)
                subs[H]=(U,W)
    hs=sorted(subs,key=lambda s:(len(s),tuple(sorted(s))))
    masks=[sum(1<<x for x in H) for H in hs]; dist=[999]*len(hs);saved=[-999]*len(hs);dist[0]=0;saved[0]=0
    edges=big=0;checked_isotropy=0
    for j,H in enumerate(hs):
        U,W=subs[H];ub=basis(U)
        for k in range(j):
            K=hs[k];idx=len(H)//len(K)
            if idx not in (3,9) or masks[k]&masks[j]!=masks[k]:continue
            UK,WK=subs[K]
            if any(bt[x][y] not in WK for x in basis(UK) for y in ub):continue
            if idx==9 and not any(cent[bar[x]] not in K for x in H):continue
            edges+=1;inc=int(idx==9);big+=inc
            dist[j]=min(dist[j],dist[k]+1);saved[j]=max(saved[j],saved[k]+inc)
            if inc:
                assert len(U)==3*len(UK) and len(W)==3*len(WK)
                forms=[a for a in range(1,q) if all(F.tr(F.mul(a,w))==0 for w in WK)]
                assert forms
                for a in forms:
                    assert all(F.tr(F.mul(a,bt[x][y]))==0 for x in ub for y in ub)
                    checked_isotropy+=1
                assert len(U)<=9
    assert len(hs[-1])==N and dist[-1]==4 and saved[-1]==2
    assert all(dist[i]<999 for i in range(len(hs)))
    # Abelian comparator: (C_9)^3 has three cyclic factors, so rho cannot be omitted.
    abelian_chain_orders=[1,9,81,729];assert len(abelian_chain_orders)-1==3
    return {'p':3,'d':3,'polynomial':F.f,'group_order':N,'subspaces':len(spaces),'subgroups':len(hs),'normal_cyclic_edges':edges,'order_p_squared_edges':big,'annihilator_isotropy_checks':checked_isotropy,'minimum_cyclic_length':dist[-1],'maximum_p_squared_factors':saved[-1],'abelian_control_cyclic_length':3,'limits':'Exhaustive subgroup enumeration uses the proved (U,W,lifts) parametrization; associativity checked only on displayed basis triples. Uniform theorem is not established by this computation.'}

def main():
    return {'form_checks':[form_checks(p,d) for p,d in [(3,3),(3,5),(5,3)]],'small_group':small_group()}
if __name__=='__main__':print(json.dumps(main(),indent=2,sort_keys=True))
