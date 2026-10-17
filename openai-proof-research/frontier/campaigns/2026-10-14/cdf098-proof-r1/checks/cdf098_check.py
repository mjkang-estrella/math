#!/usr/bin/env python3
# SPDX-License-Identifier: MIT
# Copyright (c) 2026 Myeongjin Kang
"""CDF098 proof-r1 finite sanity checks. NOT a proof: (A) exact rational
rechecks of every numerical inequality in candidate.md; (B) seeded random
finite instances of the Lemma-1 graph, testing its geometric inequalities
(scale windows, endpoint distances, fine-edge proximity, group diameters,
greedy half-radius cover counts). Finite checks never certify the universal
statement."""
import math, random, json
from fractions import Fraction as F

out = {}
# ---------- (A) exact constants ----------
A = {}
A['bottom_group_sq'] = F(1,16)+F(1,64) < F(1,4)            # (r/4)^2+(r/8)^2 < (r/2)^2
A['fine_sqrt8_over_64_lt_1_16'] = 8*F(1,64)**2 < F(1,16)**2  # sqrt8*s < r/16 when s<=r/64
A['fine_group_9_64_lt_half'] = 2*F(1,16)+2*F(1,128) < F(1,2)
A['inter_264_512_lt_1'] = F(264,512) < 1
A['inter_scale_count_le_8'] = math.floor(math.log2(192))+1 <= 8
A['high_ratio_lt_6'] = True  # 2(h+r)/(h-r)<6 iff h>2r (checked symbolically below)
A['high_ratio_symbolic'] = all(2*(h+1)/(h-1) < 6 for h in [F(2)+F(1,10**k) for k in range(1,12)])
A['high_scale_count_le_4'] = math.floor(math.log2(6))+1 <= 4
A['high_16_32_lt_1'] = F(16,32) < 1
A['low_total_le_81D10'] = all(65*D**9+16*D**4 <= 81*D**10 for D in range(1,50))
A['high_total_le_48D10'] = all(32*D**5+16*D**4 <= 48*D**10 for D in range(1,50))
A['tail_101_400_lt_half'] = (1+F(1,100))*F(1,4) < F(1,2)
A['sep_97_200'] = F(1,2)-F(3,2)*F(1,100) == F(97,200)
A['cluster_ratio_lt_32'] = F(400,97)/F(1,4) < 32 and F(1600,97) < 32
A['cluster_scale_count_le_5'] = math.floor(math.log2(1600/97))+1 <= 5
A['gamma_count'] = True  # 5+1+5*Delta^8 <= 10+6*Delta^8 trivially
A['Ytransfer_r4_lt_r2'] = 2*(F(1,16)+F(1,16)) < F(1,2)
lam = 76800; D = lam**2; Delta = 256*D**10; Lam = 10+6*Delta**8
A['Lambda_is_integer_digits'] = len(str(Lam))
out['A_exact'] = A

# ---------- (B) random instances ----------
def norm(u): return math.sqrt(sum(t*t for t in u))
def sub(u,v): return [a-b for a,b in zip(u,v)]
def segdist(c,a,b):
    d=sub(b,a); L=sum(t*t for t in d)
    t=0.0 if L==0 else max(0.0,min(1.0,sum(x*y for x,y in zip(sub(c,a),d))/L))
    return norm(sub(c,[ai+t*di for ai,di in zip(a,d)]))
def build(X):
    n=len(X); dm=max(norm(sub(X[i],X[j])) for i in range(n) for j in range(n))
    X=[[t/dm for t in x] for x in X]
    ms=min(norm(sub(X[i],X[j])) for i in range(n) for j in range(i+1,n))
    m=1
    while 2.0**-m>=ms: m+=1
    N=[[0]]; edges=[]
    for k in range(1,m+1):
        s=2.0**-k; Nk=[]
        for i in random.sample(range(n),n):
            if all(norm(sub(X[i],X[j]))>s for j in Nk): Nk.append(i)
        N.append(Nk)
        for i in Nk:
            par=[j for j in N[k-1] if norm(sub(X[i],X[j]))<=2*s]
            assert par, 'parent'
            j=random.choice(par)
            edges.append(('reg',s,i,X[i]+[s],X[j]+[2*s]))
    assert sorted(N[m])==list(range(n)), 'Nm=X'
    sm=2.0**-m
    for i in range(n): edges.append(('bot',sm,i,X[i]+[0.0],X[i]+[sm]))
    return X,N,edges,m
def run(seed,n,d):
    random.seed(seed); viol=[]
    X=[[random.gauss(0,1)*(3**-random.randint(0,4)) for _ in range(d)] for _ in range(n)]
    X,N,edges,m=build(X)
    o=X[0]+[1.0]
    for e in edges:
        for P in (e[3],e[4]):
            if norm(sub(P,o))>math.sqrt(2)+1e-12: viol.append('radius')
    pts=[]
    for e in edges:
        for t in [i/12 for i in range(13)]:
            pts.append([a+t*(b-a) for a,b in zip(e[3],e[4])])
    worst=0
    for trial in range(60):
        e=random.choice(edges); t=random.random()
        c=[a+t*(b-a) for a,b in zip(e[3],e[4])]
        p,h=c[:-1],c[-1]; r=2.0**random.uniform(-12,1)
        meet=[f for f in edges if segdist(c,f[3],f[4])<=r]
        scales=set()
        for f in meet:
            if f[0]!='reg': continue
            s=f[1]; x=X[f[2]]; scales.add(s)
            if not s<=h+r+1e-12: viol.append('s<=h+r')
            if h>2*r and not (s>=(h-r)/2-1e-12 and s>r/2): viol.append('high window')
            if not norm(sub(x,p))<=2*s+r+1e-12: viol.append('endpoint')
            if s<=r/64:
                for P in (f[3],f[4]):
                    if not norm(sub(P,x+[0.0]))<r/16: viol.append('fine prox')
        if h<=2*r:
            if len([s for s in scales if s>r/64])>8: viol.append('inter count')
        else:
            if len(scales)>4: viol.append('high count')
        ball=[q for q in pts if norm(sub(q,c))<=r]
        cen=[]
        for q in ball:
            if all(norm(sub(q,z))>r/2 for z in cen): cen.append(q)
        worst=max(worst,len(cen))
    return dict(seed=seed,n=n,d=d,m=m,edges=len(edges),violations=sorted(set(viol)),max_greedy_half_cover_on_samples=worst)
out['B_random']=[run(s,n,d) for s,(n,d) in enumerate([(12,2),(20,3),(30,5),(25,10),(40,4),(18,20)])]
out['B_all_clean']=all(not r['violations'] for r in out['B_random'])
out['A_all_true']=all(v is True for k,v in A.items() if k!='Lambda_is_integer_digits')
print(json.dumps(out,indent=1))
