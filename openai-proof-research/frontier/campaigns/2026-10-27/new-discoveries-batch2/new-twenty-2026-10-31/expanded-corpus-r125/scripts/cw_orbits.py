# Search +-1 perfect sequences with zeros (circulant weighing matrices) of prime length p, weight w,
# invariant under a multiplier t (signs constant on <t>-orbits); then classify supports up to affine maps x->ax+b.
import sys, itertools, json
p, w, t = int(sys.argv[1]), int(sys.argv[2]), int(sys.argv[3])
orbits = []; seen = set()
for x in range(p):
    if x in seen: continue
    o = []; y = x
    while y not in o: o.append(y); y = y*t % p
    orbits.append(o); seen.update(o)
def perfect(c):
    for g in range(1, p):
        if sum(c[x]*c[(x+g) % p] for x in range(p)) != 0: return False
    return True
def canon(S):
    best = None
    for a in range(1, p):
        for b in range(p):
            T = tuple(sorted((a*x+b) % p for x in S))
            if best is None or T < best: best = T
    return best
found = {}
for r in range(1, len(orbits)+1):
    for comb in itertools.combinations(range(len(orbits)), r):
        if sum(len(orbits[i]) for i in comb) != w: continue
        for signs in itertools.product((1, -1), repeat=r-1):
            c = [0]*p
            for k, i in enumerate(comb):
                s = 1 if k == 0 else signs[k-1]
                for x in orbits[i]: c[x] = s
            if perfect(c):
                S = [x for x in range(p) if c[x]]
                key = canon(S)
                found.setdefault(key, c)
print('p', p, 'w', w, 'multiplier', t, 'orbit sizes', sorted(len(o) for o in orbits))
print('inequivalent supports found:', len(found))
for k, c in found.items(): print(' support', list(k), '\n  sequence', c)
