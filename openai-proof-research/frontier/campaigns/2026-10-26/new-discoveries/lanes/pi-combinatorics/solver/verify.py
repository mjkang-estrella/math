#!/usr/bin/env python3
"""Verify a board dict is a valid Game of Cycles gameboard:
simple connected plane graph, all vertices deg >= 2, bounded faces are simple
cycles, Euler formula holds, every edge lies on exactly 2 face-walks
(bounded faces + outer walk)."""
import json, sys
from collections import defaultdict, Counter

def verify(bd):
    edges = [tuple(e) for e in bd['edges']]
    assert all(len(e) == 2 and e[0] != e[1] for e in edges), "self loop/bad edge"
    es = set(edges)
    assert len(es) == len(edges), "duplicate edges"
    n = max(v for e in edges for v in e) + 1
    deg = Counter()
    adj = defaultdict(set)
    for u, v in edges:
        deg[u] += 1; deg[v] += 1
        adj[u].add(v); adj[v].add(u)
    # connected
    seen = {0}
    st = [0]
    while st:
        x = st.pop()
        for y in adj[x]:
            if y not in seen: seen.add(y); st.append(y)
    assert len(seen) == n, "not connected (or isolated vertex numbering)"
    assert min(deg.values()) >= 2, f"min degree {min(deg.values())} < 2"
    # faces are simple cycles with consecutive edges
    for f in bd['faces']:
        k = len(f)
        assert len(set(f)) == k >= 3, "face not simple cycle"
        for i in range(k):
            a, b = f[i], f[(i+1) % k]
            assert tuple(sorted((a,b))) in es, f"face edge {a}-{b} missing"
    # edge incidence: each edge in exactly 2 walk-sides
    inc = Counter()
    for f in bd['faces'] + bd.get('dead', []):
        k = len(f)
        for i in range(k):
            a, b = f[i], f[(i+1) % k]
            inc[tuple(sorted((a,b)))] += 1
    ow = bd['outer']
    for i in range(len(ow)):
        a, b = ow[i], ow[(i+1) % len(ow)]
        inc[tuple(sorted((a,b)))] += 1
    for e in edges:
        assert inc[e] == 2, f"edge {e} on {inc[e]} walk-sides"
    # Euler: V - E + F = 2, F = #bounded + 1
    V, E, Fb = n, len(edges), len(bd['faces'])
    Fdead = len(bd.get('dead', []))
    assert V - E + Fb + Fdead + 1 == 2, f"Euler fails: V={V} E={E} Fb={Fb} Fd={Fdead}"
    # Rotation-system consistency: face walks must induce a well-defined cyclic
    # order of incident edges at each vertex, and that rotation system's faces
    # must be exactly the claimed bounded faces + outer walk.
    # At vertex v, face walk ... p, v, s ... means: in v's rotation, s is
    # immediately after p (consistent orientation).
    succ = {}  # dart (v -> s) : required predecessor position
    # represent rotation as permutation next Dart: dart (v,w) -> (v,x) where x
    # is next after w. From walk: at v, after coming from p (dart p->v), the
    # walk leaves via s (dart v->s). In an oriented embedding, the face walk
    # follows: next dart after (v->s) is (v->s') where... standard: face walk
    # traverses darts; the successor of dart (v->s) in the SAME face is the
    # dart (s->t) (move along). The rotation is encoded via: dart (p->v) and
    # (v->s) adjacent in same face => in rotation at v, (v->s) comes
    # immediately after reversed dart (v->p)?  Use standard construction:
    # rotation permutation rho on darts: rho(v->w) = (w->x)?? Simplest:
    # derive each vertex's cyclic order from the faces, assuming faces given
    # CW: at v, neighbors in order encountered ... p then s means s follows p
    # in ccw order (or cw; pick convention), then verify the induced face set.
    rot_next = {}  # (v, w) -> (v, x): x immediately after w at v
    conflict = False
    for f in list(bd['faces']) + [ow] + list(bd.get('dead', [])):
        k = len(f)
        for i in range(k):
            p, v, s = f[i-1], f[i], f[(i+1) % k]
            key = (v, p)
            if key in rot_next and rot_next[key] != (v, s):
                conflict = True
            rot_next[key] = (v, s)
    assert not conflict, "rotation conflict at some vertex"
    # completeness: every dart (v,w) with deg(v)>1 must have a successor
    for v in range(n):
        for w in adj[v]:
            if deg[v] > 1:
                assert (v, w) in rot_next, f"missing rotation successor at {v} for dart to {w}"
    # compute faces from rotation system and compare with claimed
    # face permutation on darts: from dart (v->w), face-walk successor is:
    # take rho^{-1}: the dart whose rotation-successor is (v->w)... standard:
    # next dart in face after (v->w) is (w->x) where x = rot_next[(w, v)]... 
    # Let's derive: face walk ... p, v, s ...: dart (p->v) then (v->s). Also
    # rot_next[(v,p)] = (v,s). So face successor of dart (p->v) is (v->s) =
    # rot_next[(v,p)]. i.e. face_succ((p->v)) = (v -> rot_next[(v,p)][1]).
    def face_succ(d):
        p, v = d
        return (v, rot_next[(v, p)][1])
    darts = [(u, v) for u in range(n) for v in adj[u]]
    undart = set(darts)
    seen2 = set()
    faces_from_rot = []
    for d in darts:
        if d in seen2: continue
        cyc = [d]
        seen2.add(d)
        x = face_succ(d)
        while x != d:
            assert x in undart
            cyc.append(x); seen2.add(x)
            x = face_succ(x)
        # cyclic vertex sequence
        vs = [d[0]] + [d[1] for d in cyc[:-1]]
        # rotate to canonical (start at min vertex)
        mi = vs.index(min(vs))
        vs = vs[mi:] + vs[:mi]
        faces_from_rot.append(vs)
    claimed = [list(f) for f in bd['faces']] + [list(ow)] + [list(f) for f in bd.get('dead', [])]
    def norm(f):
        r = f[::-1]  # direction-insensitive: face walk may be traversed either way
        mi = r.index(min(r))
        return tuple(r[mi:] + r[:mi])
    a = sorted(norm(f) for f in faces_from_rot)
    b2 = sorted(norm(f) for f in claimed)
    assert a == b2, f"face set mismatch:\nrot: {a}\nclaimed: {b2}"
    return True

if __name__ == '__main__':
    import glob
    ok = 0; bad = 0
    for fn in sorted(glob.glob('violation_*.json')):
        bd = json.load(open(fn))
        try:
            verify(bd)
            m = len(bd['edges'])
            print(f"{fn}: VALID board, m={m}, faces={[len(f) for f in bd['faces']]}")
            ok += 1
        except AssertionError as ex:
            print(f"{fn}: INVALID: {ex}")
            bad += 1
    print(f"{ok} valid, {bad} invalid")
