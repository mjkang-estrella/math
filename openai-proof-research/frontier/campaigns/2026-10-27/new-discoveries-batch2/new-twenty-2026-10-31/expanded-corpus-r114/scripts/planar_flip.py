# Exact enumeration of maximal planar graphs (sphere triangulations) on n vertices via BFS on the
# edge-flip graph (connected by Wagner's theorem), with isomorphism classes identified by the
# minimum embedding BFS code over all directed edges and both orientations (exact for 3-connected
# plane graphs: Whitney's theorem, embedding unique up to reflection).  Checks Conjecture 9.5(i) of
# arXiv:2506.07264 (MathDB 368745): s+(G) >= 3n for n >= 10.
import sys, json, numpy as np
n = int(sys.argv[1]); k = n - 2; N, S = k, k + 1
rot = {i: [(i + 1) % k, N, (i - 1) % k, S] for i in range(k)}
rot[N] = list(range(k))  # chosen so that faces are consistently oriented; verified below
rot[S] = [(k - 1 - j) for j in range(k)]

def faces(rot):
    seen = set(); fs = []
    for u in rot:
        for v in rot[u]:
            if (u, v) in seen: continue
            f = []; a, b = u, v
            while (a, b) not in seen:
                seen.add((a, b)); f.append(a)
                r = rot[b]; c = r[(r.index(a) - 1) % len(r)]; a, b = b, c
            fs.append(f)
    return fs

fs = faces(rot)
assert len(fs) == 2 * n - 4 and all(len(f) == 3 for f in fs), (len(fs), [len(f) for f in fs])

def code(rot):
    best = None
    for u in rot:
        for v in rot[u]:
            for d in (1, -1):
                lab = {u: 0}; order = [(u, v)]; out = []; qi = 0
                while qi < len(order):
                    w, r = order[qi]; qi += 1; L = rot[w]; i0 = L.index(r); m = len(L)
                    for t in range(m):
                        x = L[(i0 + d * t) % m]
                        if x not in lab: lab[x] = len(lab); order.append((x, w))
                        out.append(lab[x])
                    out.append(-1)
                    if best is not None and out > best[:len(out)]: break
                else:
                    if best is None or out < best: best = out
                    continue
    return tuple(best)

def flips(rot):
    for u in rot:
        for v in rot[u]:
            if u > v or len(rot[u]) < 4 or len(rot[v]) < 4: continue
            L = rot[u]; i = L.index(v); x = L[i - 1]; y = L[(i + 1) % len(L)]
            if y in rot[x]: continue
            R = {w: list(l) for w, l in rot.items()}
            R[u].remove(v); R[v].remove(u)
            for (p, q, z) in ((x, u, y), (y, v, x)):
                Lp = R[p]; a = Lp.index(q); b = Lp.index(u if q == v else v)
                # u and v are consecutive in rot[p]; insert z between them
                if (a + 1) % len(Lp) == b: Lp.insert(a + 1, z)
                elif (b + 1) % len(Lp) == a: Lp.insert(b + 1, z)
                else: raise RuntimeError('not consecutive')
            yield R

start = code(rot); seen = {start: rot}; queue = [rot]; qi = 0
while qi < len(queue):
    R = queue[qi]; qi += 1
    for R2 in flips(R):
        c = code(R2)
        if c not in seen:
            f2 = faces(R2); assert len(f2) == 2 * n - 4 and all(len(f) == 3 for f in f2)
            seen[c] = R2; queue.append(R2)
mats = []
for R in queue:
    A = np.zeros((n, n))
    for u in R:
        for v in R[u]: A[u, v] = 1
    mats.append(A)
ev = np.linalg.eigvalsh(np.array(mats)); sp = (np.where(ev > 0, ev, 0) ** 2).sum(axis=1) - 3 * n
j = int(np.argmin(sp))
res = dict(n=n, triangulations=len(queue), min_splus_minus_3n=float(sp[j]), violations=int((sp < -1e-9).sum()),
           argmin_degrees=sorted(len(queue[j][u]) for u in queue[j]), argmin_rotation={str(a): b for a, b in queue[j].items()})
json.dump(res, open(sys.argv[2], 'w'), indent=1)
print(n, len(queue), round(float(sp[j]), 6), res['violations'], res['argmin_degrees'])
