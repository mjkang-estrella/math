# 367397 (Bosma et al. Conjecture 5). Two independent checks, NOT a substitute for the written proof:
# (a) the greedy sequence S_{1,g,g+1} (bitset construction) equals the conjectured set T on [1,N];
# (b) every finite residue lemma used in the proof, checked exhaustively per g.
import sys
def greedy(g,N):
    S=[1,g,g+1]; ones=0; twos=0; threes=0
    def add(a):
        nonlocal ones,twos,threes
        threes|=twos<<a; twos|=ones<<a; ones|=1<<a
    for a in S: add(a)
    z=g+2
    while z<=N:
        if not (threes>>z)&1: S.append(z); add(z)
        z+=1
    return set(S)
def T(g,N):
    m=10*g+3; R=set(range(g,2*g+1))|set(range(6*g+2,7*g+2))
    return {z for z in range(1,N+1) if z in (1,2*g+1,6*g+1) or z%m in R}
bad=[]
for g in range(2,41):
    N=12*(10*g+3)
    if greedy(g,N)!=T(g,N): bad.append(('greedy',g))
for g in range(2,121):
    m=10*g+3; A=range(g,2*g+1); B=range(6*g+2,7*g+2); R=set(A)|set(B); sp=[1,2*g+1,6*g+1]
    blk=list(A)+list(B)
    # (II) residue-avoidance: sums of three residues, blocks with repetition, each special at most once.
    sums=set()
    for x in blk:
        for y in blk:
            sums.add((x+y)%m)
    two_blk=sums; s3=set()
    for t in two_blk:
        for x in blk: s3.add((t+x)%m)
        for s in sp: s3.add((t+s)%m)
    for i,s in enumerate(sp):
        for s2 in sp[i+1:]:
            for x in blk: s3.add((s+s2+x)%m)
    s3.add(sum(sp)%m)
    if s3&R: bad.append(('II',g))
    # (II) specials: 2g+1 and 6g+1 are not sums of three distinct smaller T-elements (direct).
    small=[z for z in range(1,6*g+1) if z in (1,2*g+1) or z%m in R]
    if any(a+b+c in (2*g+1,6*g+1) for i,a in enumerate(small) for j,b in enumerate(small[i+1:],i+1) for c in small[j+1:]): bad.append(('spec',g))
    # (III) level 0: each non-T z in (g+1,m) is a sum of three distinct smaller T-elements.
    Tl=[z for z in range(1,2*m) if z in (1,2*g+1,6*g+1) or z%m in R]
    for z in range(g+2,m):
        if z in Tl: continue
        if not any(z-a-b in Tl and z-a-b>b for a in Tl for b in Tl if a<b and a+b<z): bad.append(('III0',g,z))
    # (III) level q>=1: explicit representation families used in the proof.
    W=[1]+list(range(g,2*g+2))+list(range(6*g+1,7*g+2))
    P={a+b for a in W for b in W if a<b}
    need=set(range(0,g))|set(range(2*g+1,6*g+2))|set(range(7*g+2,10*g+3))
    for r in need:
        if r<g: ok=any(r+m-x in P for x in B) and all(True for _ in [0])
        elif r<=6*g+1: ok=any(r-x in {a+b for a in [1]+list(range(g,2*g+2)) for b in range(g,2*g+2) if a<b} for x in A)
        else: ok=any(r-x in P for x in A)
        if not ok: bad.append(('IIIq',g,r))
    # distinctness for r<g branch: need s1,s2 in [g,2g+1], s1!=s2, x in B with x+s1+s2=r+m
    for r in range(0,g):
        if not any(r+m-x-s1 in range(g,2*g+2) and r+m-x-s1!=s1 for x in B for s1 in range(g,2*g+2)): bad.append(('IIIq_small',g,r))
print('greedy==T for g in 2..40 up to 12m; lemmas for g in 2..120; failures:',bad[:10])
sys.exit(1 if bad else 0)
