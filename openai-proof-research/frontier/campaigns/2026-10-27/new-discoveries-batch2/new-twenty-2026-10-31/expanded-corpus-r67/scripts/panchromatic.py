# Brute-force diagnostic for MathDB 372105 (Conjecture 1 of arXiv:2512.15486).
# Computes chi_p, alpha_{chi_p}, chi_p^2 exactly by exhaustive enumeration of colourings.
import itertools, math, json, pathlib, sys
D = pathlib.Path(__file__).resolve().parents[1]

def panchromatic(f, E, k):
    return all({f[v] for v in e} >= set(range(k)) for e in E)

def stats(n, E):
    maxk = min(len(e) for e in E)
    chi = 0; chi2 = 0; alpha = {}
    for k in range(1, maxk + 1):
        best = None; bip = False
        for f in itertools.product(range(k), repeat=n):
            if not panchromatic(f, E, k): continue
            cnt = [f.count(c) for c in range(k)]
            u = sum(1 for c in cnt if c == 1)
            best = u if best is None else min(best, u)
            if u == 0 and all(c >= 2 for c in cnt): bip = True
        if best is not None: chi = k; alpha[k] = best
        if bip: chi2 = k
    a = alpha[chi]
    return dict(chi_p=chi, alpha=a, chi_p2=chi2, formula=chi - math.ceil(a / 2), holds=(chi2 == chi - math.ceil(a / 2)))

if __name__ == '__main__':
    E = [{0, 1, 2, 3}, {0, 1, 2, 4}, {0, 1, 2, 5}]
    r = stats(6, E); print('H6', r)
    # Exhaustive search over all hypergraphs on <=5 vertices with edges of size >=2 (small), for minimality evidence.
    out = {'H6': {'vertices': 6, 'edges': [sorted(e) for e in E], **r}}
    for n in range(2, 6):
        subsets = [frozenset(c) for s in range(2, n + 1) for c in itertools.combinations(range(n), s)]
        bad = 0; tot = 0
        for m in range(1, 4):
            for Es in itertools.combinations(subsets, m):
                tot += 1
                if not stats(n, Es)['holds']: bad += 1
        out[f'all_n{n}_upto3edges'] = dict(hypergraphs=tot, counterexamples=bad); print(n, tot, bad, flush=True)
    (D / 'outputs/panchromatic.json').write_text(json.dumps(out, indent=2) + '\n')
