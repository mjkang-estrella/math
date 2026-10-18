# Author: Myeongjin Kang. No affiliation. SPDX-License-Identifier: MIT
"""Exact finite diagnostics; not proofs of either full research target."""
import itertools as it
import json
from fractions import Fraction

S = ['cabbbca', 'aaccbb', 'cbacbca', 'bbacbb']
def overlap(a, b):
    return max(k for k in range(min(len(a), len(b)) + 1) if a[len(a)-k:] == b[:k])
def join_path(words, order):
    out = words[order[0]]
    for i, j in zip(order, order[1:]):
        out += words[j][overlap(words[i], words[j]):]
    return out

def forced_counts(words):
    """Literal finite descending recurrence from source128 eqs extension/period-rule."""
    V = {w[i:j] for w in words for i in range(len(w)) for j in range(i+1,len(w)+1)}
    alphabet = sorted(set(''.join(words)))
    counts = {}
    def B(inner, period):
        p = len(period)
        total = 0
        for r in V:
            if len(r) < len(inner)+2:
                continue
            for j in range(1,len(r)-len(inner)):
                if (r[j:j+len(inner)] == inner
                    and all(r[h] == period[(h-j)%p] for h in range(1,len(r)-1))
                    and r[0] != period[-j%p]
                    and r[-1] != period[(len(r)-1-j)%p]):
                    total += counts[r]
        return total
    for w in sorted(V,key=lambda w:(-len(w),w)):
        lower = [int(w in words),sum(counts.get(c+w,0) for c in alphabet),sum(counts.get(w+c,0) for c in alphabet)]
        for v in V:
            if len(v) <= len(w) or not v.startswith(w):
                continue
            for p in range(1,len(v)):
                if (len(v)-len(w))%p or not all(v[h] == v[h%p] for h in range(len(v))):
                    continue
                if counts[v] > B(v,v[:p]):
                    lower.append(B(w,v[:p])+(len(v)-len(w))//p+1)
        counts[w] = max(lower)
    return sum(counts[c] for c in alphabet)

def run():
    union = S + [w[::-1] for w in S]
    assert len(set(union)) == 8
    assert all(a not in b for i,a in enumerate(union) for j,b in enumerate(union) if i != j)
    n=len(S)
    perms=list(it.permutations(range(n)))
    ders=[p for p in perms if all(i != p[i] for i in range(n))]
    rows=[]
    for bits in it.product((0,1),repeat=n):
        words=[s[::-1] if b else s for s,b in zip(S,bits)]
        path,order=min((len(join_path(words,p)),p) for p in perms)
        cycle,successors=min((sum(len(words[i])-overlap(words[i],words[p[i]]) for i in range(n)),p) for p in ders)
        witness=join_path(words,order)
        assert all(w in witness for w in words)
        W=forced_counts(words)
        assert W <= path
        rows.append(dict(bits=''.join(map(str,bits)),path=path,cycle=cycle,forced_W=W,path_order=order,path_witness=witness,cycle_successors=successors))
    opt=min(r['path'] for r in rows)
    cyc=min(r['cycle'] for r in rows)
    chosen=min(r['path'] for r in rows if r['cycle']==cyc)
    assert (opt,cyc,chosen)==(18,17,19)
    assert forced_counts(['aaaa'])==4
    # Enumerate all nonempty rectangles of the 4x4 equality matrix.
    masks=range(1,16)
    rectangles=[]
    for a,b in it.product(masks,repeat=2):
        cells=[(i,j) for i in range(4) for j in range(4) if a>>i&1 and b>>j&1]
        if all(i==j for i,j in cells):
            rectangles.append(cells)
    assert len(rectangles)==4 and all(len(r)==1 for r in rectangles)
    # Exponent balance in the source's stated one-tape architecture.
    beta=Fraction(2,5)
    assert 1-Fraction(3,2)*beta==beta
    return dict(status='PASS',scope='finite exact diagnostics only; no full theorem',instance=S,complement='identity',orientation_rows=rows,OPT_RC=opt,min_cycle=cyc,best_path_at_min_cycle=chosen,min_W_at_min_cycle=min(r['forced_W'] for r in rows if r['cycle']==cyc),equality_b2_nonempty_accepting_rectangles=rectangles,one_tape_balanced_exponent=str(beta))
if __name__=='__main__':
    print(json.dumps(run(),indent=2,sort_keys=True))
