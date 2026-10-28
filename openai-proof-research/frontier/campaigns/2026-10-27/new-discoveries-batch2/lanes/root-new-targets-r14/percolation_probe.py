"""Bounded numerical search; configurations enumerated, probabilities floating.

No discovery follows from finding no trigger. Only a trigger would be rechecked
with exact rational probabilities and rigorous Poisson bounds.
"""
from pathlib import Path
import itertools
import json
import numpy as np
from scipy.special import gammaincinv

ROOT = Path(__file__).resolve().parent


def main():
    n = 6
    edges = list(itertools.combinations(range(n),2))
    masks = np.arange(1 << len(edges), dtype=np.uint32)
    bits = ((masks[None,:] >> np.arange(len(edges), dtype=np.uint32)[:,None]) & 1).astype(bool)
    lookup = np.array([i.bit_count() for i in range(1 << len(edges))],dtype=np.uint8)
    flows = np.full(len(masks),n,dtype=np.uint8)
    for middle in range(1 << (n-2)):
        side = {0} | {j+2 for j in range(n-2) if (middle>>j)&1}
        cut = sum(1<<i for i,(a,b) in enumerate(edges) if (a in side)!=(b in side))
        flows = np.minimum(flows,lookup[masks & cut])
    assert flows[0] == 0 and flows[-1] == n-1
    # A single length-two path has flow one; two disjoint paths flow two.
    def emask(es):
        return sum(1<<edges.index(tuple(sorted(e))) for e in es)
    assert flows[emask([(0,2),(1,2)])] == 1
    assert flows[emask([(0,2),(1,2),(0,3),(1,3)])] == 2
    rng = np.random.default_rng(20261028)
    worst = None
    triggers = []
    tested = 0
    for trial in range(601):
        if trial == 0:
            p = np.full(len(edges),0.5)
        elif trial < 201:
            p = rng.uniform(0.02,0.98,len(edges))
        elif trial < 401:
            p = np.clip(rng.beta(.35,.35,len(edges)),1e-4,1-1e-4)
        else:
            p = rng.integers(0,17,len(edges))/16
        weights = np.prod(np.where(bits,p[:,None],1-p[:,None]),axis=0)
        dist = np.bincount(flows,weights=weights,minlength=n)
        assert abs(float(dist.sum())-1)<1e-10
        tails = np.array([dist[k:].sum() for k in range(1,n)])
        lambdas = gammaincinv(np.arange(1,n),tails)
        for k in range(n-2):
            if not (1e-12<tails[k]<1-1e-12 and 1e-12<tails[k+1]<1-1e-12):
                continue
            tested += 1
            gap = float(lambdas[k]-lambdas[k+1])
            rec = dict(trial=trial,k=k+1,gap=gap,p=p.tolist(),tails=tails.tolist(),lambdas=lambdas.tolist())
            if worst is None or gap<worst['gap']:
                worst=rec
            if gap < -1e-8:
                triggers.append(rec)
    out=dict(status='numerical reconnaissance only',vertices=n,edges=edges,configurations=len(masks),
             trials=601,usable_comparisons=tested,triggers=triggers,worst=worst,
             interpretation='No trigger is not a theorem or an exhaustive parameter check.')
    (ROOT/'percolation-probe.json').write_text(json.dumps(out,indent=2)+'\n')
    print(json.dumps({k:v for k,v in out.items() if k not in ['edges','worst','triggers']},indent=2))
    print('trigger count',len(triggers),'smallest gap',worst['gap'] if worst else None)


if __name__ == '__main__':
    main()
