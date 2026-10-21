"""Finite exact diagnostics, MIT. Read-only: emits JSON to stdout, opens no files.
No result here is a universal robust-prophet guarantee or an independent review.
"""
from fractions import Fraction as F
from itertools import permutations, product
from math import prod
import json

class Matroid:
    def __init__(self, cols):
        self.n=len(cols);self.E=(1<<self.n)-1;self.r=[]
        for S in range(1<<self.n):
            piv={}
            for i,v in enumerate(cols):
                if not (S>>i)&1:continue
                while v:
                    k=v.bit_length()-1
                    if k in piv:v^=piv[k]
                    else:piv[k]=v;break
            self.r.append(len(piv))
        self.flats=[S for S in range(self.E+1) if self.cl(S)==S]
    def cl(self,S):return sum(1<<i for i in range(self.n) if self.r[S|1<<i]==self.r[S])
    def minbasis(self,A,P,w):
        target=self.r[A|P]-self.r[P]
        return min(sum(w[i] for i in range(self.n) if B>>i&1) for B in range(self.E+1)
                   if not B&~A and B.bit_count()==target and self.r[P|B]-self.r[P]==target)
    def tau(self,A,P,e,w):
        if self.cl(P)>>e&1:return 0
        for x in sorted(set(w[i] for i in range(self.n) if A>>i&1)):
            L=sum(1<<i for i in range(self.n) if A>>i&1 and w[i]<=x)
            if self.cl(P|L)>>e&1:return x
        return None

def mul(a,b):
    c=[F(0)]*(len(a)+len(b)-1)
    for i,x in enumerate(a):
        for j,y in enumerate(b):c[i+j]+=x*y
    return c

def expectation(vals,p):
    n=len(p)
    return sum(F(vals[A])*prod(p[j] if A>>j&1 else 1-p[j] for j in range(n)) for A in range(1<<n))

def interpolate(vals,c,t):
    n=len(c);total=F(0)
    for e in range(n):
        for A in range(1<<n):
            if A>>e&1:continue
            poly=[F(vals[A|1<<e]-vals[A])*(t[e]-c[e])]
            for j in range(n):
                if j==e:continue
                poly=mul(poly,[c[j],t[j]-c[j]] if A>>j&1 else [1-c[j],c[j]-t[j]])
            total+=sum(x/F(i+1) for i,x in enumerate(poly))
    return total

def source_layers(M,w,H,D,C,kappa,parity):
    U=0
    for e in range(M.n):
        higher=sum(1<<j for j in range(M.n) if H>>j&1 and (w[j],-j)>(w[e],-e))
        if w[e]>0 and not H>>e&1 and not M.cl(higher)>>e&1:U|=1<<e
    levels=sorted({w[e] for e in range(M.n) if (U&D)>>e&1})
    # Integer w are already rounded group weights; no floating logarithms.
    groups=[sum(1<<e for e in range(M.n) if U>>e&1 and w[e]==v) for v in levels]
    m=len(groups);low=-3*m-3;ks=list(range(low,2));L=M.cl(0)
    prev={k:(M.E if k>=0 else L) for k in ks};xs=[]
    for h,G in enumerate(groups,1):
        Dh=D&G;Ch=C&G;a=-3*h
        def Q(P):
            opts=[Z for Z in M.flats if Z&P==P]
            best=max((Z&Dh).bit_count()-kappa*M.r[Z] for Z in opts)
            return max((Z for Z in opts if (Z&Dh).bit_count()-kappa*M.r[Z]==best),key=int.bit_count)
        X={k:(Q(prev[k]) if k>=a else prev[k]) for k in ks}
        nxt={k:(M.cl(X[k]|(Ch&X[k+1])) if k<1 else M.E) for k in ks}
        xs.append(X);prev=nxt
    layers={};assignment={}
    for h,G in enumerate(groups,1):
        for e in range(M.n):
            if not G>>e&1 or (H|D|C)>>e&1:continue
            b=next(k for k in range(low,1) if xs[h-1][k]>>e&1)
            if b < -3*h+2 or b%2!=parity or prev[b-2]>>e&1:continue
            assignment[e]=b
            if b not in layers:layers[b]=[prev[b-2],0]
            layers[b][1]|=1<<e
    return layers,assignment

def main():
    mats=[Matroid(v) for v in [(0,1,1,1),(1,1,1,1),(1,2,3,3),(1,2,4,7),(1,2,4,8),(0,1,2,3)]]
    weights=[(0,1,2,4),(1,1,3,9),(1,2,4,8)]
    insertion=tail=interp=0
    for M in mats:
        for w in weights:
            for P in range(M.E+1):
                for A in range(M.E+1):
                    if P&A:continue
                    g=M.minbasis(A,P,w)
                    levels=sorted({0,*[w[j] for j in range(M.n) if A>>j&1]})
                    integral=0
                    for lo,hi in zip(levels,levels[1:]):
                        lower=sum(1<<j for j in range(M.n) if A>>j&1 and w[j]<=lo)
                        integral+=(hi-lo)*(M.r[P|A]-M.r[P|lower])
                    assert integral==g;tail+=1
                    for e in range(M.n):
                        if (P|A)>>e&1:continue
                        tau=M.tau(A,P,e,w)
                        diff=w[e] if tau is None else -max(0,tau-w[e])
                        assert M.minbasis(A|1<<e,P,w)-g==diff;insertion+=1
            vals=[M.minbasis(A,0,w) for A in range(M.E+1)]
            c=[F(1,7),F(2,5),F(3,4),F(1,2)];t=[F(1,3)]*4
            assert expectation(vals,t)-expectation(vals,c)==interpolate(vals,c,t);interp+=1
    setups=testsets=orders=nonempty=0
    mask_cases=[(H,D,C) for H,D,C in product(range(16),repeat=3) if (13*H+7*D+3*C)%67==0]
    for M in mats:
        for w in [(1,1,4,4),(0,1,4,16)]:
            for kappa in (2,2**100):
                for H,D,C in mask_cases:
                    for parity in (0,1):
                        layers,assignment=source_layers(M,w,H,D,C,kappa,parity);setups+=1
                        nonempty+=bool(assignment)
                        for T in range(16):
                            exact=sum(M.minbasis(A&T,P,w) for P,A in layers.values())
                            rewards=[]
                            for order in permutations(range(4)):
                                chosen={b:0 for b in layers};whole=0
                                for e in order:
                                    if e not in assignment or not T>>e&1:continue
                                    b=assignment[e];P=layers[b][0];A=chosen[b]
                                    if M.r[P|A|1<<e]>M.r[P|A]:
                                        chosen[b]|=1<<e;whole|=1<<e
                                    assert M.r[whole]==whole.bit_count()
                                rewards.append(sum(w[e] for e in range(4) if whole>>e&1));orders+=1
                            assert min(rewards)==exact;testsets+=1
    # Positive-probability source-compatible rank-one preprocessing state.
    M=Matroid((1,1,1,1));w=(1,1,64,64)
    layers,assignment=source_layers(M,w,0,(1<<0)|(1<<2),0,2,0)
    assert set(assignment)=={1,3} and len(layers)==1
    vals=[sum(M.minbasis(A&T,P,w) for P,A in layers.values()) for T in range(16)]
    t=F(1,8);K=8;c=t/(K*(1-t)+t)
    q=[t,c,t,t];actual=[t]*4
    ref=expectation(vals,q);got=expectation(vals,actual)
    assert got-ref==(t-c)*(1-64*t)<0
    closed_cases=0
    for m in range(1,7):
        for q in (F(1,57),F(1,8),F(2,3)):
            val=F(0)
            for bits in product((0,1),repeat=m+1):
                prob=prod(q if z else 1-q for z in bits[:m])*(t if bits[m] else 1-t)
                val+=prob*(1 if any(bits[:m]) else (64 if bits[m] else 0))
            assert val==1+(64*t-1)*(1-q)**m;closed_cases+=1
    H=2**160;ts=F(1,2**140);cs=ts/(K*(1-ts)+ts)
    w2=(1,1,H,H)
    ls,ass=source_layers(M,w2,0,5,0,2**100,0)
    assert set(ass)=={1,3} and len(ls)==1
    vals2=[sum(M.minbasis(A&T,P,w2) for P,A in ls.values()) for T in range(16)]
    realdiff=expectation(vals2,[ts]*4)-expectation(vals2,[ts,cs,ts,ts])
    assert realdiff==(ts-cs)*(1-H*ts)<0
    print(json.dumps({'status':'finite diagnostics only','rank_tail_cases':tail,'insertion_cases':insertion,
      'exact_polynomial_interpolations':interp,'source_preprocessing_states':setups,'nonempty_states':nonempty,
      'source_test_sets':testsets,'source_permutations':orders,'source_compatible_loss_example':
      {'K':K,'t':str(t),'matched_low_rate':str(c),'matched_payoff':str(ref),'actual_payoff':str(got),'difference':str(got-ref)},
      'parallel_layer_closed_form_cases':closed_cases,
      'actual_source_constants_example':{'kappa':'2^100','t':'2^-140','B':'2^32','H':'B^5','exact_difference':str(realdiff)},
      'limits':'GF(2) matroids on four labels only. Test kappa=2 or source 2^100. No performance extrapolation.'},indent=2))

if __name__=='__main__':main()
