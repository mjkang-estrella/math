# Independent reviewer code for MathDB 329080 (chord-review-r1).
# Written from the source definitions (arXiv:1410.6148 Section 2, Lemma 3.1); it does NOT import
# or copy the discovery lane's scripts.  Pure python3, run with -I.
#
# Models:
#  * RIBBON (6n half-edges): the thickened diagram F is a ribbon graph of the cubic graph
#    (2n backbone vertices, 2n backbone arcs, n chords).  At vertex i the half-edges are
#    P_i (arc to i-1), N_i (arc to i+1), C_i (chord).  A band end on the inner circle gives the
#    rotation N->C->P->N, on the outer circle N->P->C->N.  b(F) = #orbits of rho o theta
#    (face tracing).  This model is convention-free up to a global mirror.
#  * DART (2n darts, the model claimed by the discovery lane, re-implemented from the prose of
#    outputs/329080-proof.md section 2 only): sigma(i) = next endpoint on the same side,
#    increasing cyclic order for inner (bit 0), decreasing for outer (bit 1);
#    b = #cycles(sigma o tau) + [no inner endpoint] + [no outer endpoint].
#  genus g = (n - b + 2)/2 (Lemma 3.1).
import sys, json, itertools, time, re

def matchings(L):
    """All perfect matchings of 0..L-1 as partner tuples."""
    t = [-1] * L
    def rec():
        try:
            i = t.index(-1)
        except ValueError:
            yield tuple(t); return
        for j in range(i + 1, L):
            if t[j] == -1:
                t[i] = j; t[j] = i
                yield from rec()
                t[i] = -1; t[j] = -1
    yield from rec()

def canon(t):
    """Canonical form under rotation and reflection (renaming is implicit for matchings)."""
    L = len(t)
    d = [(t[i] - i) % L for i in range(L)]
    r = [(L - d[(-j) % L]) % L for j in range(L)]
    best = None
    for s in (d, r):
        for k in range(L):
            c = tuple(s[k:] + s[:k])
            if best is None or c < best: best = c
    return best

def from_canon(c):
    L = len(c); return tuple((i + c[i]) % L for i in range(L))

def from_word(w):
    pos = {}
    for i, a in enumerate(w): pos.setdefault(a, []).append(i)
    t = [0] * len(w)
    for a, (p, q) in pos.items(): t[p] = q; t[q] = p
    return tuple(t)

def word(t):
    lab = {}; out = []
    for i in range(len(t)):
        j = min(i, t[i])
        if j not in lab: lab[j] = len(lab) + 1
        out.append(lab[j])
    return ''.join(str(x) if x < 10 else chr(87 + x) for x in out)

def ncycles(perm):
    L = len(perm); seen = bytearray(L); c = 0
    for i in range(L):
        if not seen[i]:
            c += 1; x = i
            while not seen[x]: seen[x] = 1; x = perm[x]
    return c

def ribbon_b(t, mask):
    L = len(t); H = 3 * L
    theta = [0] * H; rho = [0] * H
    for i in range(L):
        P, N, C = 3 * i, 3 * i + 1, 3 * i + 2
        theta[N] = 3 * ((i + 1) % L); theta[P] = 3 * ((i - 1) % L) + 1; theta[C] = 3 * t[i] + 2
        if (mask >> i) & 1 == 0:   # inner
            rho[N] = C; rho[C] = P; rho[P] = N
        else:                      # outer
            rho[N] = P; rho[P] = C; rho[C] = N
    return ncycles([rho[theta[h]] for h in range(H)])

def sigma_of_mask(L, mask):
    side = [(mask >> i) & 1 for i in range(L)]
    sig = [0] * L
    for i in range(L):
        st = 1 if side[i] == 0 else -1
        j = (i + st) % L
        while side[j] != side[i]: j = (j + st) % L
        sig[i] = j
    extra = (1 if mask == 0 else 0) + (1 if mask == (1 << L) - 1 else 0)  # an empty circle
    return sig, extra

def dart_b(t, mask, sig=None):
    L = len(t)
    sg, extra = sigma_of_mask(L, mask)
    return ncycles([sg[t[i]] for i in range(L)]) + extra

class DartTable:
    """Precomputed sigma tables (bytes, padded to 256) for masks with top bit 0 (mirror symmetry)."""
    def __init__(self, L, half=True):
        self.L = L; self.tabs = []
        M = 1 << (L - 1) if half else 1 << L
        for m in range(M):
            sg, ex = sigma_of_mask(L, m)
            self.tabs.append((bytes(sg) + bytes(256 - L), ex))
    def bvals(self, t):
        tb = bytes(t); L = self.L
        for tab, ex in self.tabs:
            p = tb.translate(tab)
            seen = bytearray(L); c = ex
            for i in range(L):
                if not seen[i]:
                    c += 1; x = i
                    while not seen[x]: seen[x] = 1; x = p[x]
            yield c

def crosses(t, a, b):
    a1, a2 = sorted((a, t[a])); b1, b2 = sorted((b, t[b]))
    return (a1 < b1 < a2 < b2) or (b1 < a1 < b2 < a2)

def chords(t): return [(i, t[i]) for i in range(len(t)) if i < t[i]]

def bipartite(t):
    ch = chords(t); n = len(ch)
    adj = [[j for j in range(n) if j != i and crosses(t, ch[i][0], ch[j][0])] for i in range(n)]
    col = [-1] * n
    for s in range(n):
        if col[s] >= 0: continue
        col[s] = 0; st = [s]
        while st:
            u = st.pop()
            for v in adj[u]:
                if col[v] < 0: col[v] = 1 - col[u]; st.append(v)
                elif col[v] == col[u]: return False
    return True

def gr_ribbon(t):
    L = len(t); n = L // 2
    return sorted({(n - ribbon_b(t, m) + 2) // 2 for m in range(1 << L)})

def delete(t, k):
    """Delete the chord through endpoint k; return (new partner tuple, kept positions)."""
    L = len(t); a, b = k, t[k]
    keep = [i for i in range(L) if i != a and i != b]
    idx = {p: j for j, p in enumerate(keep)}
    return tuple(idx[t[p]] for p in keep), keep

def insert(t, i, j):
    """Insert a new chord with endpoints placed before old positions i <= j (i,j in 0..L)."""
    w = list(range(len(t)))
    lab = [min(p, t[p]) for p in range(len(t))]
    new = lab[:i] + ['x'] + lab[i:j] + ['x'] + lab[j:]
    return from_word(new)

def P5(t):
    """Predicate of the 5-chord lemma, implemented from its prose (Lemma 4 (a) and (b))."""
    L = len(t); ch = chords(t); n = len(ch)
    X = [[crosses(t, ch[i][0], ch[j][0]) for j in range(n)] for i in range(n)]
    a_ok = any(not any(X[i][j] for j in range(n) if j != i) for i in range(n))
    if not a_ok: return False
    for T in itertools.combinations(range(n), 3):
        if not (X[T[0]][T[1]] and X[T[0]][T[2]] and X[T[1]][T[2]]): continue
        tri = set(p for k in T for p in ch[k])
        def arc(p):  # label an arc by the triangle endpoint that precedes it cyclically
            q = (p - 1) % L
            while q not in tri: q = (q - 1) % L
            return q
        labels = set()
        for k in range(n):
            if k in T: continue
            p, q = ch[k]
            if not ((q - p) % L == 1 or (p - q) % L == 1): return False
            if arc(p) != arc(q): return False
            labels.add(arc(p))
        if len(labels) != 1: return False
    return True

R3U = lambda n: from_word([1, 2, 3, 1, 2, 3] + [k for k in range(4, n + 1) for _ in (0, 1)])

def log(o): print(json.dumps(o, sort_keys=True), flush=True)

# ---------------------------------------------------------------- modes
def mode_xval(nmax):
    """Per-mask equality of DART and RIBBON models on ALL labelled matchings and ALL masks."""
    for n in range(1, nmax + 1):
        L = 2 * n; tot = bad = 0; t0 = time.time()
        for t in matchings(L):
            for m in range(1 << L):
                tot += 1
                if ribbon_b(t, m) != dart_b(t, m): bad += 1
        log({'mode': 'xval', 'n': n, 'pairs': tot, 'mismatches': bad, 'sec': round(time.time() - t0, 1)})

def mode_xval_classes(n):
    """Same, but on one representative per equivalence class (for n = 6)."""
    L = 2 * n; reps = sorted({canon(t) for t in matchings(L)}); tot = bad = 0; t0 = time.time()
    for c in reps:
        t = from_canon(c)
        for m in range(1 << L):
            tot += 1
            if ribbon_b(t, m) != dart_b(t, m): bad += 1
    log({'mode': 'xval_classes', 'n': n, 'classes': len(reps), 'pairs': tot, 'mismatches': bad,
         'sec': round(time.time() - t0, 1)})

def mode_local(nmax):
    """Ribbon model: (i) deleting any chord changes b by exactly +-1;
    (ii) flipping one endpoint side changes b by 0 or +-2; (iii) global flip preserves b;
    (iv) parity b = n mod 2.  On class representatives, all masks."""
    for n in range(1, nmax + 1):
        L = 2 * n; reps = sorted({canon(t) for t in matchings(L)})
        cnt = {'del': 0, 'del_bad': 0, 'flip_bad': 0, 'mirror_bad': 0, 'parity_bad': 0}
        for c in reps:
            t = from_canon(c)
            B = [ribbon_b(t, m) for m in range(1 << L)]
            full = (1 << L) - 1
            for m in range(1 << L):
                if (B[m] - n) % 2: cnt['parity_bad'] += 1
                if B[m ^ full] != B[m]: cnt['mirror_bad'] += 1
                for i in range(L):
                    if abs(B[m ^ (1 << i)] - B[m]) not in (0, 2): cnt['flip_bad'] += 1
            for k in range(L):
                if k > t[k]: continue
                td, keep = delete(t, k)
                for m in range(1 << L):
                    mm = sum(((m >> p) & 1) << j for j, p in enumerate(keep))
                    bd = ribbon_b(td, mm) if n > 1 else 2  # empty diagram: annulus, b = 2
                    cnt['del'] += 1
                    if abs(bd - B[m]) != 1: cnt['del_bad'] += 1
        cnt.update({'mode': 'local', 'n': n, 'classes': len(reps)}); log(cnt)

def mode_gr(nmax, model):
    """Genus ranges of all classes; GR_n sets; {1,2} diagrams; bipartite <-> min 0."""
    for n in range(1, nmax + 1):
        L = 2 * n; t0 = time.time()
        reps = sorted({canon(t) for t in matchings(L)})
        DT = DartTable(L) if model == 'dart' else None
        GR = {}; g12 = []; bip_bad = 0; interval_bad = 0
        for c in reps:
            t = from_canon(c)
            if model == 'ribbon':
                gs = gr_ribbon(t)
            else:
                gs = sorted({(n - b + 2) // 2 for b in DT.bvals(t)})
            if gs != list(range(gs[0], gs[-1] + 1)): interval_bad += 1
            key = '{' + ','.join(map(str, gs)) + '}'
            GR[key] = GR.get(key, 0) + 1
            if gs == [1, 2]: g12.append(word(t))
            if (gs[0] == 0) != bipartite(t): bip_bad += 1
        log({'mode': 'gr', 'model': model, 'n': n, 'classes': len(reps), 'GR_counts': GR,
             'gr12_words': g12, 'bipartite_iff_min0_failures': bip_bad,
             'non_interval': interval_bad, 'sec': round(time.time() - t0, 1)})

def mode_gr_chunk(n, k, K):
    """GR_n for classes with index = k mod K (dart model, mirror-halved masks)."""
    L = 2 * n; t0 = time.time()
    reps = sorted({canon(t) for t in matchings(L)})
    DT = DartTable(L); GR = {}; g12 = []; cnt = 0; interval_bad = 0
    for idx, c in enumerate(reps):
        if idx % K != k: continue
        t = from_canon(c); cnt += 1
        gs = sorted({(n - b + 2) // 2 for b in DT.bvals(t)})
        if gs != list(range(gs[0], gs[-1] + 1)): interval_bad += 1
        key = '{' + ','.join(map(str, gs)) + '}'
        GR[key] = GR.get(key, 0) + 1
        if gs == [1, 2]: g12.append(word(t))
    log({'mode': 'gr_chunk', 'n': n, 'chunk': k, 'of': K, 'classes_total': len(reps),
         'classes_done': cnt, 'GR_counts': GR, 'gr12_words': g12, 'non_interval': interval_bad,
         'sec': round(time.time() - t0, 1)})

def mode_base5(lean_path):
    L = 10; n = 5; t0 = time.time()
    Pc = 0; notP = []; bad = []; maxg = {}
    for t in matchings(L):
        mg = max((n - ribbon_b(t, m) + 2) // 2 for m in range(1 << L))
        p = P5(t)
        maxg[t] = mg
        if p: Pc += 1
        else: notP.append(t)
        if mg <= 2 and not p: bad.append(word(t))
    # the triangle case of (b) equals "isomorphic to (123123)(4455)"
    target = canon(from_word([1, 2, 3, 1, 2, 3, 4, 4, 5, 5]))
    tri_bad = 0
    for t in matchings(L):
        ch = chords(t)
        has_tri = any(all(crosses(t, ch[a][0], ch[b][0]) for a, b in itertools.combinations(T, 2))
                      for T in itertools.combinations(range(5), 3))
        if maxg[t] <= 2 and has_tri and canon(t) != target: tri_bad += 1
    classes = {}
    for t, mg in maxg.items(): classes.setdefault(canon(t), mg)
    low = sorted(word(from_canon(c)) for c, mg in classes.items() if mg <= 2)
    # lane certificate (Base5Data.lean): parse text only, check each witness in the RIBBON model
    txt = open(lean_path, encoding='utf-8').read()
    ents = re.findall(r'\(\[([0-9, ]+)\],\s*([0-9]+)\)', txt)
    wit_ok = 0; wit_bad = []; wset = set()
    for ws, ms in ents:
        w = [int(x) for x in ws.split(',')]; m = int(ms); t = from_word(w); wset.add(t)
        if ribbon_b(t, m) == 1 and not P5(t): wit_ok += 1
        else: wit_bad.append((w, m))
    r3 = from_word([1, 2, 3, 1, 2, 3])
    r3_planar = sum(1 for m in range(64) if ribbon_b(r3, m) == 5)
    log({'mode': 'base5', 'matchings': 945 if Pc + len(notP) == 945 else Pc + len(notP),
         'P_holds': Pc, 'not_P': len(notP), 'maxgenus_le2_but_not_P': bad,
         'maxgenus_le2_count_labelled': sum(1 for v in maxg.values() if v <= 2),
         'triangle_case_not_R3_4455': tri_bad,
         'classes': len(classes), 'classes_maxgenus_le2': len(low), 'classes_maxgenus_le2_words': low,
         'lane_witness_entries': len(ents), 'lane_witness_valid': wit_ok, 'lane_witness_invalid': wit_bad,
         'lane_witness_cover_exactly_notP': wset == set(notP),
         'R3_masks_with_5_faces': r3_planar, 'sec': round(time.time() - t0, 1)})

def maxg_le2(t, DT, n):
    """True iff no mask gives genus >= 3 (b <= n - 4).  Also returns the genus set if True."""
    lim = n - 4; gs = set()
    for b in DT.bvals(t):
        if b <= lim: return False, None
        gs.add((n - b + 2) // 2)
    return True, sorted(gs)

def mode_hered(nmax, state_path=None):
    """Hereditary enumeration of C_n = {classes with max genus <= 2}; complete by heredity."""
    C = {1: {canon((1, 0))}}
    for n in range(2, nmax + 1):
        L = 2 * n; t0 = time.time(); DT = DartTable(L)
        cand = set()
        for c in C[n - 1]:
            t = from_canon(c)
            for i in range(L - 1):
                for j in range(i, L - 1):
                    cand.add(canon(insert(t, i, j)))
        pre = []
        for c in cand:
            t = from_canon(c)
            if all(canon(delete(t, k)[0]) in C[n - 1] for k in range(L) if k < t[k]): pre.append(c)
        Cn = set(); g12 = []
        for c in sorted(pre):
            ok, gs = maxg_le2(from_canon(c), DT, n)
            if ok:
                Cn.add(c)
                if gs == [1, 2]: g12.append(word(from_canon(c)))
        C[n] = Cn
        log({'mode': 'hered', 'n': n, 'candidates': len(cand), 'after_prefilter': len(pre),
             '|C_n|': len(Cn), 'gr12_words': sorted(g12),
             'gr12_is_R3U': sorted(g12) == [word(from_canon(canon(R3U(n))))] if n >= 3 else None,
             'sec': round(time.time() - t0, 1)})

def mode_hered_from(n, prev_json):
    """One level of the hereditary search, seeded by the previous level's C_{n-1} (canonical tuples)."""
    prev = {tuple(x) for x in json.load(open(prev_json))}
    L = 2 * n; t0 = time.time(); DT = DartTable(L)
    cand = set()
    for c in prev:
        t = from_canon(c)
        for i in range(L - 1):
            for j in range(i, L - 1):
                cand.add(canon(insert(t, i, j)))
    pre = [c for c in cand
           if all(canon(delete(from_canon(c), k)[0]) in prev for k in range(L) if k < from_canon(c)[k])]
    Cn = set(); g12 = []
    for c in sorted(pre):
        ok, gs = maxg_le2(from_canon(c), DT, n)
        if ok:
            Cn.add(c)
            if gs == [1, 2]: g12.append(word(from_canon(c)))
    log({'mode': 'hered_from', 'n': n, 'prev': len(prev), 'candidates': len(cand),
         'after_prefilter': len(pre), '|C_n|': len(Cn), 'gr12_words': sorted(g12),
         'gr12_is_R3U': sorted(g12) == [word(from_canon(canon(R3U(n))))],
         'sec': round(time.time() - t0, 1)})
    return Cn

def mode_hered_dump(nmax, out):
    C = {canon((1, 0))}
    for n in range(2, nmax + 1):
        L = 2 * n; DT = DartTable(L); cand = set()
        for c in C:
            t = from_canon(c)
            for i in range(L - 1):
                for j in range(i, L - 1): cand.add(canon(insert(t, i, j)))
        pre = [c for c in cand if all(canon(delete(from_canon(c), k)[0]) in C
                                      for k in range(L) if k < from_canon(c)[k])]
        C = {c for c in pre if maxg_le2(from_canon(c), DT, n)[0]}
    json.dump(sorted(C), open(out, 'w'))
    log({'mode': 'hered_dump', 'n': nmax, '|C_n|': len(C), 'out': out})

def mode_transfer(mmax):
    """Ribbon-model check of the lane's transfer rules for D_m = 123123 a1a1...amam.
    State: d = b - m, s = [the two sides of the end edge lie on one face]."""
    out = {}
    for m in range(0, mmax + 1):
        n = 3 + m; t = R3U(n); L = 2 * n
        states = set(); gs = set()
        for mask in range(1 << L):
            b = ribbon_b(t, mask); gs.add((n - b + 2) // 2)
        out[m] = sorted(gs)
    # rule check: append one chord at the end edge, all four side choices
    viol = 0; checked = 0
    def state(t, mask):
        L = len(t); H = 3 * L
        theta = [0] * H; rho = [0] * H
        for i in range(L):
            P, N, C = 3 * i, 3 * i + 1, 3 * i + 2
            theta[N] = 3 * ((i + 1) % L); theta[P] = 3 * ((i - 1) % L) + 1; theta[C] = 3 * t[i] + 2
            if (mask >> i) & 1 == 0: rho[N] = C; rho[C] = P; rho[P] = N
            else: rho[N] = P; rho[P] = C; rho[C] = N
        phi = [rho[theta[h]] for h in range(H)]
        lab = [-1] * H; f = 0
        for h in range(H):
            if lab[h] < 0:
                x = h
                while lab[x] < 0: lab[x] = f; x = phi[x]
                f += 1
        # end edge = arc from vertex L-1 to vertex 0: half-edges N_{L-1} and P_0, i.e. its two sides
        return f, lab[3 * (L - 1) + 1] == lab[0]
    for m in range(0, min(mmax, 3) + 1):
        n = 3 + m; t = R3U(n); L = 2 * n; t2 = R3U(n + 1)
        for mask in range(1 << L):
            b, s = state(t, mask); d = b - m
            for e in range(4):
                mask2 = mask | (e << L)
                b2, s2 = state(t2, mask2); d2 = b2 - (m + 1)
                checked += 1
                if e in (0, 3): exp = (d, s)
                else: exp = (d, True) if s else (d - 2, True)
                if (d2, s2) != exp: viol += 1
    base = set()
    for mask in range(64):
        b, s = state(R3U(3), mask); base.add((b, s))
    log({'mode': 'transfer', 'gr_D_m': out, 'rule_checks': checked, 'rule_violations': viol,
         'base_states_D0': sorted(base)})

if __name__ == '__main__':
    a = sys.argv[1:]
    {'xval': lambda: mode_xval(int(a[1])),
     'xval_classes': lambda: mode_xval_classes(int(a[1])),
     'local': lambda: mode_local(int(a[1])),
     'gr': lambda: mode_gr(int(a[1]), a[2]),
     'gr_chunk': lambda: mode_gr_chunk(int(a[1]), int(a[2]), int(a[3])),
     'base5': lambda: mode_base5(a[1]),
     'hered': lambda: mode_hered(int(a[1])),
     'hered_dump': lambda: mode_hered_dump(int(a[1]), a[2]),
     'hered_from': lambda: mode_hered_from(int(a[1]), a[2]),
     'transfer': lambda: mode_transfer(int(a[1])),
     }[a[0]]()
