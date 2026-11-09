"""Fresh exhaustive search: which graphs of order <= 9 have a path P_m (m >= 3) or a cycle
C_m (m >= 5) as IR-graph?  Written in this lane; imports no other lane's code.

All graphs are included, connected or not.  Non-isomorphic graphs of order n are generated as
one-vertex extensions of the non-isomorphic graphs of order n-1, deduplicated by a canonical form
(individualisation-refinement; branching is pruned only by twin transpositions, which are
automorphisms fixing every individualised vertex).  Order 9 is covered by evaluating every
one-vertex extension (all 256 neighbourhoods) of every non-isomorphic graph of order 8; every
9-vertex graph arises this way up to isomorphism (delete any vertex).

Modes (outputs are opened with mode 'x', never overwritten):
  small OUT               orders 1..7: classes and IR-graph evaluation of every class
  gen8 SMALL LO HI OUT    canonical forms of all extensions of order-7 classes [LO,HI)
  merge8 OUT SMALL IN...  merge gen8 chunks into the order-8 classes; evaluate every class
  ext9 MERGE8 LO HI OUT   evaluate every extension of order-8 classes [LO,HI)
  agg OUT MERGE8 IN...    aggregate ext9 chunks; isomorphism classes of the hits
"""
import sys
sys.dont_write_bytecode = True
import json, time, hashlib

T0 = time.time()


# ---------------- canonical form ----------------------------------------------------------
def refine(adj, cells):
    while True:
        masks = []
        for c in cells:
            m = 0
            for v in c:
                m |= 1 << v
            masks.append(m)
        new, changed = [], False
        for c in cells:
            if len(c) == 1:
                new.append(c)
                continue
            groups = {}
            for v in c:
                a = adj[v]
                key = tuple(bin(a & m).count("1") for m in masks)
                groups.setdefault(key, []).append(v)
            if len(groups) > 1:
                changed = True
            for k in sorted(groups):
                new.append(groups[k])
        cells = new
        if not changed:
            return cells


def canon(n, adj):
    best = [-1]

    def leaf(cells):
        order = [c[0] for c in cells]
        code = 0
        for i in range(n):
            ai = adj[order[i]]
            for j in range(i + 1, n):
                code = (code << 1) | ((ai >> order[j]) & 1)
        if code > best[0]:
            best[0] = code

    def search(cells):
        cells = refine(adj, cells)
        k = next((i for i, c in enumerate(cells) if len(c) > 1), None)
        if k is None:
            leaf(cells)
            return
        cell = cells[k]
        reps = []
        for v in cell:
            if not any((adj[v] & ~(1 << r)) == (adj[r] & ~(1 << v)) for r in reps):
                reps.append(v)
        for v in reps:
            rest = [u for u in cell if u != v]
            search(cells[:k] + [[v], rest] + cells[k + 1:])

    search([list(range(n))])
    return best[0]


# ---------------- IR-graph evaluation ---------------------------------------------------------
def ir_sets(n, N):
    """irredundant sets grown by adding a larger vertex (heredity); returns IR and the IR-sets"""
    level = [(1 << v, v, N[v], (N[v],)) for v in range(n)]
    while True:
        nxt = []
        for mask, top, U, privs in level:
            for t in range(top + 1, n):
                Nt = N[t]
                pt = Nt & ~U
                if not pt:
                    continue
                ok = True
                for p in privs:
                    if not (p & ~Nt):
                        ok = False
                        break
                if not ok:
                    continue
                nxt.append((mask | (1 << t), t, U | Nt, tuple(p & ~Nt for p in privs) + (pt,)))
        if not nxt:
            return bin(level[0][0]).count("1"), [x[0] for x in level]
        level = nxt


def classify(n, N):
    """returns (IR, number of IR-sets, label) with label 'P<m>', 'C<m>' or None"""
    IR, sets = ir_sets(n, N)
    m = len(sets)
    if m == 1:
        return IR, 1, "P1"
    deg = [0] * m
    nb = [[] for _ in range(m)]
    ne = 0
    for i in range(m):
        A = sets[i]
        for j in range(i + 1, m):
            B = sets[j]
            X = A & ~B
            if X & (X - 1):
                continue
            Y = B & ~A
            u = X.bit_length() - 1
            v = Y.bit_length() - 1
            if (N[u] >> v) & 1:          # u != v automatically; uv an edge
                deg[i] += 1; deg[j] += 1; nb[i].append(j); nb[j].append(i); ne += 1
    if max(deg) > 2:
        return IR, m, None
    seen = {0}; st = [0]
    while st:
        x = st.pop()
        for y in nb[x]:
            if y not in seen:
                seen.add(y); st.append(y)
    if len(seen) != m:
        return IR, m, None
    if ne == m - 1:
        return IR, m, "P%d" % m
    if ne == m and m >= 3:
        return IR, m, "C%d" % m
    return IR, m, None


def is_hit(label):
    return label is not None and ((label[0] == "P" and int(label[1:]) >= 3) or
                                  (label[0] == "C" and int(label[1:]) >= 5))


def closed(n, adj):
    return [adj[v] | (1 << v) for v in range(n)]


def connected(n, adj):
    seen = 1; st = [0]
    while st:
        x = st.pop()
        new = adj[x] & ~seen
        seen |= new
        while new:
            l = new & -new
            st.append(l.bit_length() - 1)
            new ^= l
    return seen == (1 << n) - 1


def extend(n, adj, S):
    return [adj[v] | (((S >> v) & 1) << n) for v in range(n)] + [S]


def from_code(n, code):
    adj = [0] * n
    bits = n * (n - 1) // 2
    k = bits - 1
    for i in range(n):
        for j in range(i + 1, n):
            if (code >> k) & 1:
                adj[i] |= 1 << j; adj[j] |= 1 << i
            k -= 1
    return adj


def nedges(adj):
    return sum(bin(a).count("1") for a in adj) // 2


def dump(path, obj):
    blob = json.dumps(obj, indent=1, sort_keys=True)
    with open(path, "x") as f:
        f.write(blob)
    return hashlib.sha256(blob.encode()).hexdigest()


def main():
    mode = sys.argv[1]
    if mode == "small":
        out = sys.argv[2]
        levels = {1: [canon(1, [0])]}
        for n in range(2, 8):
            seen = set()
            for code in levels[n - 1]:
                adj = from_code(n - 1, code)
                for S in range(1 << (n - 1)):
                    seen.add(canon(n, extend(n - 1, adj, S)))
            levels[n] = sorted(seen)
        stats, hits = {}, []
        for n, codes in levels.items():
            for code in codes:
                adj = from_code(n, code)
                IR, m, lab = classify(n, closed(n, adj))
                key = "%d:%s" % (n, lab)
                stats[key] = stats.get(key, 0) + 1
                if is_hit(lab):
                    hits.append({"n": n, "code": code, "label": lab})
        res = {"class_counts": {n: len(c) for n, c in levels.items()},
               "graphs_evaluated": sum(len(c) for c in levels.values()),
               "label_stats": stats, "hits": hits, "secs": round(time.time() - T0, 1),
               "classes": {n: c for n, c in levels.items()}}
        h = dump(out, res)
        print(json.dumps({k: res[k] for k in ["class_counts", "graphs_evaluated", "hits", "secs"]}), "sha256", h)
    elif mode == "gen8":
        small, lo, hi, out = sys.argv[2], int(sys.argv[3]), int(sys.argv[4]), sys.argv[5]
        base = json.load(open(small))["classes"]["7"]
        seen = set(); cnt = 0
        for code in base[lo:hi]:
            adj = from_code(7, code)
            for S in range(128):
                seen.add(canon(8, extend(7, adj, S))); cnt += 1
        res = {"lo": lo, "hi": min(hi, len(base)), "n_base": len(base), "extensions": cnt,
               "codes": sorted(seen), "secs": round(time.time() - T0, 1)}
        h = dump(out, res)
        print(json.dumps({"lo": lo, "hi": res["hi"], "extensions": cnt, "distinct": len(seen), "secs": res["secs"]}), "sha256", h)
    elif mode == "merge8":
        out, small, ins = sys.argv[2], sys.argv[3], sys.argv[4:]
        nbase = len(json.load(open(small))["classes"]["7"])
        allc, ranges = set(), []
        for p in ins:
            d = json.load(open(p))
            ranges.append((d["lo"], d["hi"]))
            allc.update(d["codes"])
        ranges.sort()
        assert ranges[0][0] == 0 and ranges[-1][1] == nbase and all(
            ranges[i][1] == ranges[i + 1][0] for i in range(len(ranges) - 1)), ranges
        codes = sorted(allc)
        stats, hits = {}, []
        for code in codes:
            adj = from_code(8, code)
            IR, m, lab = classify(8, closed(8, adj))
            key = "8:%s" % lab
            stats[key] = stats.get(key, 0) + 1
            if is_hit(lab):
                hits.append({"n": 8, "code": code, "label": lab})
        res = {"order7_classes": nbase, "chunk_ranges": ranges, "class_count_8": len(codes),
               "label_stats": stats, "hits": hits, "codes": codes, "secs": round(time.time() - T0, 1)}
        h = dump(out, res)
        print(json.dumps({k: res[k] for k in ["order7_classes", "class_count_8", "hits", "secs"]}), "sha256", h)
    elif mode == "ext9":
        m8, lo, hi, out = sys.argv[2], int(sys.argv[3]), int(sys.argv[4]), sys.argv[5]
        codes = json.load(open(m8))["codes"]
        hi = min(hi, len(codes))
        stats, hits, cnt = {}, [], 0
        for idx in range(lo, hi):
            adj8 = from_code(8, codes[idx])
            Nb = [adj8[v] | (1 << v) for v in range(8)]
            for S in range(256):
                N = [Nb[v] | (((S >> v) & 1) << 8) for v in range(8)] + [S | 256]
                IR, m, lab = classify(9, N)
                cnt += 1
                stats[lab or "other"] = stats.get(lab or "other", 0) + 1
                if is_hit(lab):
                    hits.append({"base_index": idx, "S": S, "IR": IR, "label": lab})
        res = {"lo": lo, "hi": hi, "n_base": len(codes), "evaluated": cnt, "label_stats": stats,
               "hits": hits, "secs": round(time.time() - T0, 1)}
        h = dump(out, res)
        print(json.dumps({"lo": lo, "hi": hi, "evaluated": cnt, "hits": len(hits),
                          "labels": sorted({x["label"] for x in hits}), "secs": res["secs"]}), "sha256", h)
    elif mode == "agg":
        out, m8, ins = sys.argv[2], sys.argv[3], sys.argv[4:]
        codes = json.load(open(m8))["codes"]
        ranges, total, hits, stats = [], 0, [], {}
        for p in ins:
            d = json.load(open(p))
            ranges.append((d["lo"], d["hi"]))
            total += d["evaluated"]
            hits.extend(d["hits"])
            for k, v in d["label_stats"].items():
                stats[k] = stats.get(k, 0) + v
        ranges.sort()
        assert ranges[0][0] == 0 and ranges[-1][1] == len(codes) and all(
            ranges[i][1] == ranges[i + 1][0] for i in range(len(ranges) - 1)), ranges
        assert total == 256 * len(codes)
        # the manuscript's graph G
        G_edges = "03 04 06 07 13 15 16 17 18 24 25 27 28 36 38 46 47 48 57 58".split()
        gadj = [0] * 9
        for e in G_edges:
            a, b = int(e[0]), int(e[1]); gadj[a] |= 1 << b; gadj[b] |= 1 << a
        Gcanon = canon(9, gadj)
        classes = {}
        for h in hits:
            adj9 = extend(8, from_code(8, codes[h["base_index"]]), h["S"])
            c = canon(9, adj9)
            rec = classes.setdefault(c, {"label": h["label"], "labelled_hits": 0, "edges": nedges(adj9),
                                         "connected": connected(9, adj9), "IR": h["IR"],
                                         "is_class_of_G": c == Gcanon})
            assert rec["label"] == h["label"]
            rec["labelled_hits"] += 1
        res = {"order8_classes": len(codes), "chunk_ranges": ranges, "labelled_graphs_evaluated": total,
               "n_hits": len(hits), "hit_labels": sorted({h["label"] for h in hits}),
               "iso_classes": sorted(classes.values(), key=lambda r: r["label"]),
               "n_iso_classes": len(classes), "label_stats": stats, "hits": hits,
               "secs": round(time.time() - T0, 1)}
        h = dump(out, res)
        print(json.dumps({k: res[k] for k in ["labelled_graphs_evaluated", "n_hits", "hit_labels", "n_iso_classes", "iso_classes", "secs"]}), "sha256", h)
    else:
        raise SystemExit("unknown mode")


if __name__ == "__main__":
    main()
