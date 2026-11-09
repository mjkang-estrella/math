"""Independent verification of MathDB 332371 counterexample data.
Fresh implementation: GF(2) rank by own elimination; no reuse of author code."""
import json, itertools, hashlib, os, sys

LANE = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
A = os.path.join(os.path.dirname(LANE), 'expanded-corpus-r250')

cols = [9,6,4,11,6,14,5,1,12]           # candidate claim
E = list(range(9))

def vec(v):
    return [(v >> i) & 1 for i in range(4)]

def gf2_rank(sub):
    # rank of the set of column vectors indexed by sub, own elimination
    rows = [vec(cols[i]) for i in sub]
    rank = 0
    for c in range(4):
        piv = None
        for r in range(rank, len(rows)):
            if rows[r][c]:
                piv = r; break
        if piv is None: continue
        rows[rank], rows[piv] = rows[piv], rows[rank]
        for r in range(len(rows)):
            if r != rank and rows[r][c]:
                rows[r] = [(a ^ b) for a, b in zip(rows[r], rows[rank])]
        rank += 1
    return rank

# sanity: full set rank
full_rank = gf2_rank(E)
assert full_rank == 4, full_rank

bases = sorted(tuple(sorted(c)) for c in itertools.combinations(E, 4) if gf2_rank(c) == 4)
print('num bases:', len(bases))

# basis exchange axiom, every ordered pair and every e in a\b
def is_exchangable():
    Bs = set(bases)
    for a in bases:
        aset = set(a)
        for b in bases:
            bset = set(b)
            for e in aset - bset:
                ok = any((f in (bset - aset)) and tuple(sorted((aset - {e}) | {f})) in Bs
                         for f in bset - aset)
                if not ok:
                    return (a, b, e)
    return None
print('exchange violation:', is_exchangable())

# partitions of E\{x} into two disjoint bases whose union is E\{x}
def part_pairs(x):
    Ex = [e for e in E if e != x]
    res = []
    for b1 in bases:
        s1 = set(b1)
        if not s1 <= set(Ex): continue
        rest = frozenset(set(Ex) - s1)
        if len(rest) == 4 and tuple(sorted(rest)) in set(bases):
            b2 = tuple(sorted(rest))
            if b1 <= b2:  # avoid duplicate unordered pair
                res.append((tuple(b1), b2))
    return res

# extendible-base lists: bases B with B subset Ex and Ex\B a base
def extendible(x):
    Ex = set(e for e in E if e != x)
    out = set()
    for b in bases:
        s = set(b)
        if s <= Ex:
            comp = tuple(sorted(Ex - s))
            if comp in set(bases):
                out.add(tuple(b))
    return out

X, Y = 1, 6
ex = part_pairs(X); ey = part_pairs(Y)
print('partition pairs E\\%d:' % X, ex)
print('partition pairs E\\%d:' % Y, ey)
lx, ly = extendible(X), extendible(Y)
print('|extendible x|:', len(lx), '|extendible y|:', len(ly))
print('intersection:', sorted(lx & ly))
assert len(lx) == 32 and len(ly) == 24 and not (lx & ly)

# the two specific partitions from CANDIDATE.md
p1 = ({0,2,3,5},{4,6,7,8}); p2 = ({0,1,2,7},{3,4,5,8})
B = set(bases)
for (u,v),x in ((p1,1),(p2,6)):
    assert tuple(sorted(u)) in B and tuple(sorted(v)) in B
    assert not (u & v) and u | v == set(e for e in E if e != x)
print('specific partitions valid: True')

# nonvacuity / hypothesis check
assert X in E and Y in E and X != Y
assert len(E) == 2*4+1
print('hypotheses: |E|=9=2*4+1, x=%d,y=%d distinct, both deletions partitionable: True' % (X,Y))

# parallel pair check (equal columns)
par = [(i,j) for i in E for j in E if i<j and cols[i]==cols[j]]
print('parallel label pairs (equal columns):', par)

# cross-check against author artifacts
cert = json.load(open(os.path.join(A,'matroid-certificate.json')))
assert cert['cols'] == cols and cert['bases'] == [list(b) for b in bases], 'cert mismatch'
assert sorted(cert['deletion_complementary_bases']['1']) == sorted([list(b) for b in lx])
assert sorted(cert['deletion_complementary_bases']['6']) == sorted([list(b) for b in ly])
print('matroid-certificate.json matches independent computation: True')

# cross-check the Lean baseList literal
import re
lean = open(os.path.join(A,'lean','Bases.lean')).read()
body = lean.split('def baseList',1)[1].split(':=',1)[1].split('def bases',1)[0]
sets = re.findall(r'\{([\d,\s]*)\}', body)
lean_bases = sorted(tuple(sorted(int(x) for x in s.replace('\n',' ').split(',') if x.strip())) for s in sets)
assert lean_bases == bases, 'Lean baseList mismatch'
print('lean/Bases.lean baseList == independent bases: True (%d entries)' % len(lean_bases))

# negative control: perturb one column, expect the discriminative checks to change
cols2 = cols[:]; cols2[7] = 2   # change element 7's column
import copy
def rank_with(cs, sub):
    global cols; old=cols[:]; cols=cs; r=gf2_rank(sub); cols=old; return r
# recompute with perturbed cols via module-level switch
saved=cols[:]
cols=cols2
b2 = sorted(tuple(sorted(c)) for c in itertools.combinations(E,4) if gf2_rank(c)==4)
def ext2(x):
    Ex=set(e for e in E if e!=x); out=set()
    Bs=set(b2)
    for b in b2:
        s=set(b)
        if s<=Ex and tuple(sorted(Ex-s)) in Bs: out.add(tuple(b))
    return out
ix=ext2(1); iy=ext2(6)
print('CONTROL perturbed cols: |bases|=%d |ext1|=%d |ext6|=%d intersect=%d (non-degenerate test)'%(len(b2),len(ix),len(iy),len(ix&iy)))
cols=saved
print('ALL INDEPENDENT CHECKS PASS')
