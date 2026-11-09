#!/usr/bin/env python3
"""Bounded seeded heuristic search for a red/blue edge coloring of the complete
multipartite host K_{5x5} (25 vertices (a,i), a,i in 0..4; 250 cross-part edges)
with NO monochromatic K_{2,5}.

Exact integer violation score:
  S = sum over the 300 unordered vertex pairs {u,v} of
      max(0, redcommon-4) + max(0, bluecommon-4)
where redcommon = #{w : w adjacent to both u,v (cross-part edges only),
                    w outside both endpoint parts, both edges uw,vw red},
and bluecommon analogously. Eligible counts: 50 same-part pairs x 20, 250
cross-part pairs x 15 = 300 pairs total.

Common neighbors are recomputed from 25-bit per-vertex masks with popcount.
The incremental flip update only reverts to mask-recomputation of the affected
pair set; it is validated against full recomputation in --selftest.

Python standard library only. Single process, single RNG stream, seed 20261105.
Hard internal stop: wall or CPU budget. Heuristic only: no completeness claim;
if the best score is > 0 that is reported as-is (never called UNSAT/a proof).
"""
import argparse, json, os, random, time, hashlib, datetime

BASE = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
N = 25            # vertices 0..24, part v//5, index v%5
NP = 5            # parts
PS = 5            # part size


def build_static():
    """Edges in lex order (u<v, different parts), var id = index+1.
    pairlist: all 300 unordered vertex pairs with eligibility mask over the
    25-vertex space (w outside both endpoint parts)."""
    edge_id = {}
    edges = []
    eid = 0
    for u in range(N):
        for v in range(u + 1, N):
            if u // PS != v // PS:
                edge_id[(u, v)] = eid
                edges.append((u, v))
                eid += 1
    assert len(edges) == 250 and eid == 250

    pairs = []   # (u, v, eligmask25)
    for u in range(N):
        for v in range(u + 1, N):
            m = 0
            for w in range(N):
                if w != u and w != v and w // PS != u // PS and w // PS != v // PS:
                    m |= 1 << w
            pairs.append((u, v, m))
    assert len(pairs) == 300
    # flip-affected pairs: flipping edge (u,v) changes counts only of pairs
    # (x,w) with x in {u,v}, w != x, part(w) != part(other), i.e. elig has the
    # other endpoint's bit AND the pair is not (u,v) itself.
    aff = [[[] for _ in range(N)] for _ in range(N)]  # aff[u][v] = pair idxs
    for pi, (a, b, m) in enumerate(pairs):
        aff[a][b].append(pi)
        aff[b][a].append(pi)
    # flip-affected pair lists, built explicitly
    flip_aff = []
    for u in range(N):
        for v in range(N):
            if u == v or u // PS == v // PS:
                flip_aff.append(())
                continue
            s = []
            for pi, (a, b, m) in enumerate(pairs):
                if a == u and (m >> v) & 1:
                    s.append(pi)
                elif b == u and (m >> v) & 1:
                    s.append(pi)
                elif a == v and (m >> u) & 1:
                    s.append(pi)
                elif b == v and (m >> u) & 1:
                    s.append(pi)
            flip_aff.append(tuple(s))
    return edges, edge_id, pairs, flip_aff


EDGES, EDGE_ID, PAIRS, FLIP_AFF = build_static()
BIT = [1 << v for v in range(N)]


def full_counts(rnb, bnb):
    """Exact (score, counts) from per-vertex mask arrays. counts: list per pair
    (cred, cblue)."""
    counts = []
    score = 0
    for a, b, m in PAIRS:
        cr = (rnb[a] & rnb[b] & m).bit_count()
        cb = (bnb[a] & bnb[b] & m).bit_count()
        counts.append((cr, cb))
        if cr > 4:
            score += cr - 4
        if cb > 4:
            score += cb - 4
    return score, counts


def recount_pair(pi, rnb, bnb):
    a, b, m = PAIRS[pi]
    return ((rnb[a] & rnb[b] & m).bit_count(), (bnb[a] & bnb[b] & m).bit_count())


def apply_flip(eid, red, rnb, bnb):
    """Flip edge eid; update supplied bits and masks; return affected pairs."""
    if red is not None:
        red[eid] = not red[eid]
    u, v = EDGES[eid]
    rnb[u] ^= BIT[v]; rnb[v] ^= BIT[u]
    bnb[u] ^= BIT[v]; bnb[v] ^= BIT[u]
    return FLIP_AFF[u * N + v]


def colors_to_masks(bits):
    """bits: list of 250 bools (True=red) in lex edge order -> (rnb, bnb)."""
    rnb = [0] * N
    bnb = [0] * N
    for e, (u, v) in enumerate(EDGES):
        if bits[e]:
            rnb[u] |= BIT[v]; rnb[v] |= BIT[u]
        else:
            bnb[u] |= BIT[v]; bnb[v] |= BIT[u]
    return rnb, bnb


# ---------------- structured initializations (heuristic seeds only) ----------
def init_circulant(rng, cycle_s, skip_s):
    """Per part-pair (a,b): red iff (j-i) mod 5 in D_ab, |D_ab| = s_ab with
    cycle-pairs s=cycle_s, skip-pairs s=skip_s. Each vertex red-degree
    2*cycle_s + 2*skip_s (10 when {2,3} assigned as 2+2+3+3)."""
    s = {}
    for a in range(NP):
        for d in (1, 4):
            s[(a, (a + d) % NP)] = cycle_s
        for d in (2, 3):
            s[(a, (a + d) % NP)] = skip_s
    choices = {(a,b): set(rng.sample(range(PS), s[(a,b)]))
               for a in range(NP) for b in range(a+1, NP)}
    bits = [False] * 250
    for e, (u, v) in enumerate(EDGES):
        a, b = u // PS, v // PS
        i, j = u % PS, v % PS
        if a > b:
            a, b, i, j = b, a, j, i
        D = choices[(a, b)]
        if ((j - i) % PS) in D:
            bits[e] = True
    return bits


def init_random(rng):
    return [rng.random() < 0.5 for _ in range(250)]


def init_degree10(rng):
    """Greedy initial edge packing with red degrees at most 10."""
    bits = [False] * 250
    deg = [0] * N
    order = list(range(250))
    rng.shuffle(order)
    for e in order:
        u, v = EDGES[e]
        if deg[u] < 10 and deg[v] < 10:
            bits[e] = True
            deg[u] += 1; deg[v] += 1
    return bits


# ---------------- the single search trajectory -------------------------------
def anneal(rng, bits, t_end, t0=1.6, t1=0.07, report=None):
    """Simulated-annealing / iterated-local-search hybrid on the exact score.
    Returns (best_score, best_bits, iters, trajectory)."""
    red = bits[:]
    rnb, bnb = colors_to_masks(red)
    score, counts = full_counts(rnb, bnb)
    best, best_bits = score, red[:]
    traj = [(0.0, score)]
    it = 0
    imp_since_kick = 0
    last_t = time.monotonic()
    while True:
        now = time.monotonic()
        cpu = time.process_time()
        if best == 0 or now >= t_end or cpu > CPU_BUDGET:
            break
        frac = min(1.0, (now - T_START) / max(1e-9, t_end - T_START))
        temp = t0 * (t1 / t0) ** frac
        # phase: mostly SA; periodic kick from best when stagnant
        it += 1
        e = rng.randrange(250)
        u, v = EDGES[e]
        aff = FLIP_AFF[u * N + v]
        # delta via mask-recount of affected pairs (validated in selftest)
        d = 0
        newcounts = []
        for pi in aff:
            a, b, m = PAIRS[pi]
            cr0, cb0 = counts[pi]
            cr1 = (rnb[a] & rnb[b] & m).bit_count() if False else None
            # recount after virtual flip: flip masks first is wrong here, so
            # compute contribution change directly
            cr1 = ((rnb[a] ^ (BIT[v] if a == u else 0) ^ (BIT[u] if a == v else 0)) &
                   (rnb[b] ^ (BIT[v] if b == u else 0) ^ (BIT[u] if b == v else 0)) & m).bit_count()
            cb1 = ((bnb[a] ^ (BIT[v] if a == u else 0) ^ (BIT[u] if a == v else 0)) &
                   (bnb[b] ^ (BIT[v] if b == u else 0) ^ (BIT[u] if b == v else 0)) & m).bit_count()
            d += max(0, cr1 - 4) - max(0, cr0 - 4)
            d += max(0, cb1 - 4) - max(0, cb0 - 4)
            newcounts.append((pi, cr1, cb1))
        if d <= 0 or rng.random() < pow(2.718281828459045, -d / temp):
            for pi, cr1, cb1 in newcounts:
                counts[pi] = (cr1, cb1)
            red[e] = not red[e]
            rnb[u] ^= BIT[v]; rnb[v] ^= BIT[u]
            bnb[u] ^= BIT[v]; bnb[v] ^= BIT[u]
            score += d
            if score < best:
                best = score
                best_bits = red[:]
                imp_since_kick = 0
            else:
                imp_since_kick += 1
        else:
            imp_since_kick += 1
        if imp_since_kick > 4000:
            # kick: perturb from best, keep best saved
            red = best_bits[:]
            rnb, bnb = colors_to_masks(red)
            score, counts = full_counts(rnb, bnb)
            for _ in range(6):
                apply_flip(rng.randrange(250), red, rnb, bnb)
            score, counts = full_counts(rnb, bnb)
            imp_since_kick = 0
        now2 = time.monotonic()
        if now2 - last_t > 2.0:
            last_t = now2
            traj.append((round(now2 - T_START, 2), score, best))
    traj.append((round(time.monotonic() - T_START, 2), score, best))
    return best, best_bits, it, traj


CPU_BUDGET = 115.0
T_START = 0.0


def main():
    global CPU_BUDGET, T_START
    ap = argparse.ArgumentParser()
    ap.add_argument('--seed', type=int, default=20261105)
    ap.add_argument('--wall-deadline', type=float, default=128.0)
    ap.add_argument('--cpu-budget', type=float, default=112.0)
    ap.add_argument('--selftest', action='store_true')
    args = ap.parse_args()
    CPU_BUDGET = args.cpu_budget
    out = {'utc_start': datetime.datetime.now(datetime.timezone.utc).isoformat(),
           'seed': args.seed, 'mathdb_id': 359209, 'host': 'K_5x5 complete multipartite, 25 vertices, 250 cross-part edges',
           'score_def': 'sum over 300 pairs of max(0,redcommon-4)+max(0,bluecommon-4); eligible w outside endpoint parts, cross-part edges only'}

    if args.selftest:
        # capped validation: incremental mask-recount vs independent full
        # recompute on random colorings and random flip sequences.
        rng = random.Random(12345)
        bad = 0
        for trial in range(200):
            bits = init_random(rng)
            rnb, bnb = colors_to_masks(bits)
            s0, c0 = full_counts(rnb, bnb)
            for _ in range(30):
                e = rng.randrange(250)
                u, v = EDGES[e]
                # virtual apply then compare
                aff = FLIP_AFF[u * N + v]
                rnb2, bnb2 = rnb[:], bnb[:]
                apply_flip(e, bits, rnb2, bnb2)
                assert colors_to_masks(bits) == (rnb2, bnb2)
                s1, c1 = full_counts(rnb2, bnb2)
                d = 0
                for pi in aff:
                    a, b, m = PAIRS[pi]
                    cr1 = (rnb2[a] & rnb2[b] & m).bit_count()
                    cb1 = (bnb2[a] & bnb2[b] & m).bit_count()
                    d += max(0, cr1 - 4) - max(0, c0[pi][0] - 4)
                    d += max(0, cb1 - 4) - max(0, c0[pi][1] - 4)
                if s0 + d != s1:
                    bad += 1
                s0, c0 = s1, c1
                rnb, bnb = rnb2, bnb2
        # static structure checks
        same_part = sum(1 for a, b, m in PAIRS if a // PS == b // PS)
        cross = 300 - same_part
        elig_ok = all(m.bit_count() == (20 if a // PS == b // PS else 15) for a, b, m in PAIRS)
        st = {'selftest': True, 'incremental_mismatches': bad, 'same_part_pairs': same_part,
              'cross_part_pairs': cross, 'eligible_counts_ok': elig_ok,
              'edges': len(EDGES), 'pairs': len(PAIRS)}
        print(json.dumps(st))
        assert bad == 0 and elig_ok and same_part == 50 and cross == 250
        return

    # -------- the one full search run --------
    T_START = time.monotonic()
    rng = random.Random(args.seed)
    inits = []
    inits.append(('circulant_2_3', init_circulant(rng, 2, 3)))
    inits.append(('circulant_3_2', init_circulant(rng, 3, 2)))
    inits.append(('random_p05', init_random(rng)))
    inits.append(('degree10', init_degree10(rng)))
    inits.append(('circulant_rand_sizes', init_circulant(rng, rng.choice([2, 3]), rng.choice([2, 3]))))
    scored = []
    for name, b in inits:
        rnb, bnb = colors_to_masks(b)
        s, _ = full_counts(rnb, bnb)
        scored.append((s, name, b))
    scored.sort(key=lambda x: x[0])
    init_summary = [{'init': nm, 'score': s} for s, nm, _ in scored]
    best_overall, best_bits_overall = None, None
    # time-sliced: 25% of budget across starts, then 75% on the best
    total = args.wall_deadline
    t_end_phase1 = T_START + total * 0.25
    per = (t_end_phase1 - T_START) / len(scored)
    ranking = []
    for s0, nm, b in scored:
        if time.monotonic() >= t_end_phase1:
            break
        t_end = min(t_end_phase1, time.monotonic() + per)
        s, bb, it, _ = anneal(rng, b, t_end)
        ranking.append((s, nm, bb))
        if best_overall is None or s < best_overall:
            best_overall, best_bits_overall = s, bb[:]
    ranking.sort(key=lambda x: x[0])
    # phase 2: long anneal from best, fresh temperature schedule
    if best_overall == 0:
        s, bb, it2, traj = best_overall, best_bits_overall, 0, []
    else:
        s, bb, it2, traj = anneal(rng, ranking[0][2], T_START + args.wall_deadline, t0=1.0, t1=0.05)
    if s < best_overall:
        best_overall, best_bits_overall = s, bb
    wall = time.monotonic() - T_START
    cpu = time.process_time()
    rnb, bnb = colors_to_masks(best_bits_overall)
    score_check, counts = full_counts(rnb, bnb)
    assert score_check == best_overall
    out.update({
        'utc_end': datetime.datetime.now(datetime.timezone.utc).isoformat(),
        'wall_s': round(wall, 3), 'cpu_s': round(cpu, 3),
        'wall_deadline_s': args.wall_deadline, 'cpu_budget_s': args.cpu_budget,
        'iterations_phase2': it2,
        'inits': init_summary,
        'phase2_start_score': ranking[0][0],
        'trajectory_tail': traj[-12:],
        'best_score': best_overall,
        'best_bits_lex': ''.join('1' if b else '0' for b in best_bits_overall),
        'bits_sha256': hashlib.sha256(''.join('1' if b else '0' for b in best_bits_overall).encode()).hexdigest(),
        'heuristic_disclaimer': 'single seeded heuristic run; score>0 is NOT an UNSAT proof or a lower-bound result',
    })
    with open(os.path.join(BASE, 'search-result.json'), 'w') as f:
        json.dump(out, f, indent=1)
    print(json.dumps({k: out[k] for k in ('best_score', 'wall_s', 'cpu_s', 'seed')}))
    # stash best bits for the checker
    with open(os.path.join(BASE, 'best-bits.json'), 'w') as f:
        json.dump({'best_score': best_overall, 'bits': ''.join('1' if b else '0' for b in best_bits_overall)}, f)

if __name__ == '__main__':
    main()
