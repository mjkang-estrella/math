#!/usr/bin/env python3
"""Independent exact verification of the order-16 and order-32 base certificates
and their complements, plus the seed matching certificates.
Usage: verify_base.py OUT.json   (inputs read from the sibling lanes, read-only)."""
import ast, json, os, sys, hashlib
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import xm

BASE = os.path.abspath(os.path.join(os.path.dirname(__file__), "..", ".."))
F = os.path.join(BASE, "xor-magic-focused-r1")
X = os.path.join(BASE, "expanded-corpus-r90")

def sha(p): return hashlib.sha256(open(p, "rb").read()).hexdigest()

def load_json_graph(p):
    d = json.load(open(p))
    return d["N"], [tuple(e) for e in d["edges"]], d.get("closed")

def load_author(p):
    """Parse the authors' inert .py.txt by AST literal evaluation only; relabel by
    the authors' own labelling vectors (bit order immaterial for zero sums)."""
    vals = {}
    for st in ast.parse(open(p).read()).body:
        if isinstance(st, ast.Assign) and len(st.targets) == 1 and isinstance(st.targets[0], ast.Name) \
                and st.targets[0].id in ("nbhd", "labeling"):
            vals[st.targets[0].id] = ast.literal_eval(st.value)
    nb, lab = vals["nbhd"], vals["labeling"]
    N = len(lab)
    code = {v: sum(b << i for i, b in enumerate(vec)) for v, vec in lab.items()}
    assert sorted(code.values()) == list(range(N)), "author labelling not bijective"
    sym = all(u in nb[v] for u in nb for v in nb[u])
    edges = sorted({(min(code[u], code[v]), max(code[u], code[v])) for u in nb for v in nb[u]})
    return N, edges, sym

def main(out):
    xm.f4_selftest()
    graphs = {
        (16, "open", 5): ("json", os.path.join(X, "outputs/xor-16-5.json")),
        (16, "open", 7): ("json", os.path.join(X, "outputs/xor-16-7.json")),
        (16, "open", 9): ("author", os.path.join(F, "sources/author-open16-9.py.txt")),
        (16, "closed", 4): ("json", os.path.join(F, "outputs/base-16-4-1.json")),
        (32, "open", 5): ("json", os.path.join(F, "outputs/seed-32-5-0.json")),
        (32, "open", 7): ("author", os.path.join(F, "sources/author-open32-7.py.txt")),
        (32, "open", 9): ("json", os.path.join(X, "outputs/xor-32-9.json")),
        (32, "open", 11): ("author", os.path.join(F, "sources/author-open32-11.py.txt")),
        (32, "open", 13): ("author", os.path.join(F, "sources/author-open32-13.py.txt")),
        (32, "open", 15): ("author", os.path.join(F, "sources/author-open32-15.py.txt")),
        (32, "open", 27): ("author", os.path.join(F, "sources/author-open32-27.py.txt")),
        (32, "closed", 4): ("json", os.path.join(F, "outputs/seed-32-4-1.json")),
        (32, "closed", 6): ("json", os.path.join(F, "outputs/symmetric-32-6.json")),
        (32, "closed", 8): ("json", os.path.join(F, "outputs/base-32-8-1.json")),
        (32, "closed", 10): ("json", os.path.join(F, "outputs/base-32-10-1.json")),
        (32, "closed", 12): ("json", os.path.join(F, "outputs/base-32-12-1.json")),
        (32, "closed", 14): ("json", os.path.join(F, "outputs/base-32-14-1.json")),
        # alternates, checked but not needed for coverage
        (32, "open", "5-alt"): ("author", os.path.join(F, "sources/author-open32-5.py.txt")),
        (32, "open", "5-alt2"): ("json", os.path.join(X, "outputs/xor-32-5.json")),
    }
    res = {"graphs": {}, "complements": {}, "coverage": {}, "seed_factors": {}}
    witnesses = {}
    for (N, typ, d), (kind, p) in graphs.items():
        if kind == "json":
            n2, edges, cl = load_json_graph(p); extra = {"declared_closed": cl}
        else:
            n2, edges, symm = load_author(p); extra = {"author_nbhd_symmetric": symm}
        assert n2 == N
        r = xm.check_graph(N, edges, typ == "closed"); r.update(extra, source=os.path.relpath(p, BASE), sha256=sha(p))
        key = f"{N}-{typ}-{d}"; res["graphs"][key] = r
        if not isinstance(d, int): continue
        assert r["degree"] == d, (key, r)
        if r["ok"]: witnesses[(N, typ, d)] = "direct " + key
        comp = xm.complement(N, edges); ctyp = "closed" if typ == "open" else "open"
        rc = xm.check_graph(N, comp, ctyp == "closed"); res["complements"][key] = rc
        if rc["ok"]: witnesses.setdefault((N, ctyp, rc["degree"]), "complement of " + key)
    for N in (16, 32):
        miss = []
        for d in range(5, N - 4, 2):
            w = witnesses.get((N, "open", d)); res["coverage"][f"{N}-open-{d}"] = w
            if not w: miss.append(("open", d))
        for d in range(4, N - 5, 2):
            w = witnesses.get((N, "closed", d)); res["coverage"][f"{N}-closed-{d}"] = w
            if not w: miss.append(("closed", d))
        # literal printed endpoint and Proposition 24 degrees must have no witness here
        res["coverage"][f"{N}-closed-{N-4}-literal-endpoint"] = witnesses.get((N, "closed", N - 4))
        res["coverage"][f"{N}-missing"] = miss
    seeds = {"16-closed-4": "outputs/base-16-4-1", "16-open-5": None, "32-closed-4": "outputs/seed-32-4-1",
             "32-open-5": "outputs/seed-32-5-0"}
    for key, stem in seeds.items():
        N, typ, d = int(key.split("-")[0]), key.split("-")[1], int(key.split("-")[2])
        if stem is None:
            gp = os.path.join(X, "outputs/xor-16-5.json"); fp = os.path.join(F, "outputs/xor-16-5-factors-")
        else:
            gp = os.path.join(F, stem + ".json"); fp = os.path.join(F, stem + "-factors-")
        _, edges, _ = load_json_graph(gp)
        f0 = json.load(open(fp + "0.json")); f1 = json.load(open(fp + "1.json"))
        assert f0["complement"] is False and f1["complement"] is True
        M = [[tuple(e) for e in m] for m in f0["factors"]]; C = [[tuple(e) for e in m] for m in f1["factors"]]
        okM = xm.check_decomposition(N, edges, M); okC = xm.check_decomposition(N, xm.complement(N, edges), C)
        cyc = [len(c) for c in xm.two_factor_cycles(N, M[0], M[1])]
        res["seed_factors"][key] = {"graph": os.path.relpath(gp, BASE), "graph_sha256": sha(gp),
            "factors_sha256": [sha(fp + "0.json"), sha(fp + "1.json")], "G_decomposition": okM, "complement_decomposition": okC,
            "num_M": len(M), "num_C": len(C), "F_cycle_lengths": cyc, "has_cycle_not_div_3": any(L % 3 for L in cyc),
            "graph_ok": xm.check_graph(N, edges, typ == "closed")["ok"]}
    res["all_ok"] = (not res["coverage"]["16-missing"] and not res["coverage"]["32-missing"]
                     and all(v["G_decomposition"][0] and v["complement_decomposition"][0] and v["has_cycle_not_div_3"] and v["graph_ok"]
                             for v in res["seed_factors"].values())
                     and res["coverage"]["16-closed-12-literal-endpoint"] is None and res["coverage"]["32-closed-28-literal-endpoint"] is None)
    json.dump(res, open(out, "w"), indent=1, sort_keys=True)
    print("all_ok", res["all_ok"]); print("missing16", res["coverage"]["16-missing"], "missing32", res["coverage"]["32-missing"])
    for k, v in res["seed_factors"].items(): print(k, v["G_decomposition"], v["complement_decomposition"], v["F_cycle_lengths"])
    for k, v in sorted(res["graphs"].items()): print(k, v["ok"], v["degree"], v["components"], "| comp:", res["complements"].get(k, {}).get("ok"), res["complements"].get(k, {}).get("degree"), res["complements"].get(k, {}).get("components"))

if __name__ == "__main__":
    main(sys.argv[1])
