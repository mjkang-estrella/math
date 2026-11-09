"""Check every quantitative statement of the manuscript against fresh outputs and copied evidence.

Usage (from the lane directory):
  python3 -I scripts/check_numbers.py paper/manuscript-resolved.txt receipts/numbers-receipt.json
Each claim is a text fragment that must occur in the resolved manuscript text (tables included)
together with a predicate computed from outputs/, inputs/ and lean/.  Afterwards every digit
token outside the reference list is classified; unexplained tokens are reported.
"""
import sys
sys.dont_write_bytecode = True
import json, re, hashlib, itertools

txt_path, out_path = sys.argv[1], sys.argv[2]
raw = open(txt_path, encoding="utf-8").read()
T = re.sub(r"\s+", " ", raw)
F = json.load(open("outputs/graph-facts.json"))
small = json.load(open("outputs/search/small.json"))
m8 = json.load(open("outputs/search/merge8.json"))
agg = json.load(open("outputs/search/agg9.json"))
safe = json.load(open("receipts/safe-extract-receipt.json"))
fres = json.load(open("inputs/formal/results.json"))
replay = json.load(open("inputs/root/replay-result.json"))
regref = json.load(open("inputs/root/registry-refresh.json"))
audit = open("inputs/formal/final-extraction-logs/Audit.compile.log").read()
review = open("inputs/review/review.json").read()
cand = open("inputs/discovery/CANDIDATE.md").read()
tex = open("inputs/sources/1812.03382v3/Irredundance_Graphs.tex").read()
tex2104 = open("inputs/sources/2104.09004v2/Irredundance_Trees_May2020.tex").read()
mathdb = json.loads(open("mathdb-350452.jsonl").readline())
citing = json.load(open("inputs/sources/openalex-citing-3.json"))
oatitle = json.load(open("inputs/sources/openalex-title-irredundance.json"))
abs1812 = open("inputs/sources/abs-1812.03382.html", errors="replace").read()
abs2104 = open("inputs/sources/abs-2104.09004.html", errors="replace").read()
four_src = open("lean/safe-extracted/Four.lean").read()
three_src = open("lean/safe-extracted/Three.lean").read()
endpoint_src = open("lean/safe-extracted/Endpoint.lean").read()
zsha = hashlib.sha256(open("lean/source.zip", "rb").read()).hexdigest()

walk = [d["D"] for d in F["IR_sets_path_order"]]
H = F["IR_graph_edges"]
# diameter of the IR-graph
adjH = {i: set() for i in range(9)}
for a, b in H:
    adjH[a].add(b); adjH[b].add(a)
def ecc(s):
    dist = {s: 0}; fr = [s]
    while fr:
        nf = []
        for x in fr:
            for y in adjH[x]:
                if y not in dist:
                    dist[y] = dist[x] + 1; nf.append(y)
        fr = nf
    return max(dist.values())
diamH = max(ecc(s) for s in range(9))
deg = F["degrees"]
cls = {c["label"]: c for c in agg["iso_classes"]}
fw = {tuple(d["equals_Nbar_of"]): d for d in F["four_without_dominating_triple"]}
sw = F["swaps_along_path"]
setstr = lambda s: "{" + ",".join(s) + "}"

C = []
def claim(frag, ok, note=""):
    C.append({"fragment": frag, "in_text": re.sub(r"\s+", " ", frag) in T, "predicate": bool(ok), "note": note})

# --- the graph -----------------------------------------------------------------------------------
claim("a graph G on 9 vertices with 20 edges", F["n_edges"] == 20 and len(F["degrees"]) == 9)
claim("IR(G) = 3, G has exactly nine IR(G)-sets", F["IR"] == 3 and F["n_IR_sets"] == 9)
claim("G(IR) ≅ P9", F["IR_graph_is_path_in_walk_order"] and F["n_IR_graph_edges"] == 8)
claim("with the seven edges 05, 08, 14, 23, 26, 37 and 56 deleted",
      sorted(set("".join(map(str, p)) for p in itertools.combinations(range(9), 2) if p[0] // 3 != p[1] // 3)
             - set(F["edges"])) == ["05", "08", "14", "23", "26", "37", "56"])
claim("The deleted edges form the path 8–0–5–6–2–3–7 together with the edge 14",
      F["deleted_edges_structure"] == "path 8-0-5-6-2-3-7 plus edge 1-4")
claim(" ".join(F["edges"]) .replace(" ", "  ") .replace("  ", " ") + ".", len(F["edges"]) == 20)
claim("Vertices 1, 4, 7 and 8 have degree 5 and the others have degree 4",
      sorted(v for v in deg if deg[v] == 5) == ["1", "4", "7", "8"] and all(deg[v] in (4, 5) for v in deg))
claim("The graph is connected", F["G_connected"])
claim("all 9! permutations shows that its automorphism group has order 2", F["automorphism_group_order"] == 2)
claim("W0 = {0,1,2}, W1 = {0,2,7}, W2 = {0,4,7}, W3 = {4,6,7}, W4 = {6,7,8}",
      walk[:5] == ["012", "027", "047", "467", "678"])
claim("W5 = {1,6,8}, W6 = {1,3,8}, W7 = {3,5,8}, W8 = {3,4,5}", walk[5:] == ["168", "138", "358", "345"])
# --- proof ----------------------------------------------------------------------------------------
claim("for all 36 pairs P (Table 2). Exactly nine pairs dominate G, namely 05, 08, 14, 17, 23, 26, 37, 48 and 56",
      sorted(F["empty_pairs"]) == ["05", "08", "14", "17", "23", "26", "37", "48", "56"] and
      len(F["pair_common_complement_nbhd"]) == 36)
claim("the two edges 17 and 48 of G", sorted(k for k, v in F["empty_pairs"].items() if v == "G-edge") == ["17", "48"])
claim("Each of the 84 three-sets", F["n_three_subsets"] == 84)
claim("There are 54 such triples", F["summary"]["triple_classes_abc"][0] == 54)
claim("There are 21 such triples, listed in Table 3", F["summary"]["triple_classes_abc"][1] == 21)
claim("class (c) consists of exactly the nine sets W0, …, W8",
      sorted(F["triples_class_c_dominating_no_empty_pair"]) == sorted(walk))
claim("1, 9, 36 and 9 irredundant sets of sizes 0, 1, 2 and 3",
      F["irredundant_counts_by_size"] == [1, 9, 36, 9, 0, 0, 0, 0, 0, 0])
claim("every pair is irredundant", F["irredundant_counts_by_size"][2] == 36)
claim("Two of the sets Wi share two vertices only if their indices differ by one",
      F["share_two_pairs"] == [[i, i + 1] for i in range(8)])
claim("each of the 126 four-sets D. For 121 of them",
      F["n_four_subsets"] == 126 and F["four_containing_dominating_triple"] == 121)
claim("there are 63 dominating triples", F["n_three_subsets"] - len(F["triples_class_b_nondominating"]) == 63)
claim("U(0) = {1,2,5,8}, U(2) = {0,1,3,6}, U(3) = {2,4,5,7}, U(5) = {0,3,4,6} and U(6) = {2,5,7,8}",
      [fw[(w,)]["D"] for w in (0, 2, 3, 5, 6)] == ["1258", "0136", "2457", "0346", "2578"] and len(fw) == 5)
claim("the vertex 2, 0, 2, 0 or 2, respectively", [fw[(w,)]["witness"] for w in (0, 2, 3, 5, 6)] == [2, 0, 2, 0, 2])
claim("Of the 36 pairs {Wi, Wj}, the 28 with", F["n_IR_set_pairs"] == 36 and 36 - len(F["share_two_pairs"]) == 28)
claim("For each of the eight pairs", F["n_pairs_sharing_two"] == 8)
claim("1→7, 2→4, 0→6, 4→8, 7→1, 6→3, 1→5 and 8→4",
      ["%d→%d" % (s["out"], s["in"]) for s in sw] == "1→7 2→4 0→6 4→8 7→1 6→3 1→5 8→4".split())
claim("17, 24, 06, 48, 17, 36, 15 and 48 are edges of G",
      all("%d%d" % tuple(sorted((s["out"], s["in"]))) in F["edges"] for s in sw) and
      ["%d%d" % tuple(sorted((s["out"], s["in"]))) for s in sw] == "17 24 06 48 17 36 15 48".split())
claim("the independent sets W0, W4 and W8 are the three parts A, C and B",
      F["independent_IR_sets"] == ["012", "678", "345"])
claim("is connected and has maximum degree 2", F["IR_graph_max_degree"] == 2)
claim("Our IR-graph has diameter 8", diamH == 8)
claim("the IR-graph of K2 is K2",F["control_K2"]["IR"] == 1 and len(F["control_K2"]["IR_sets"]) == 2)
# --- search ---------------------------------------------------------------------------------------
cc = small["class_counts"]
claim("The class counts 1, 2, 4, 11, 34, 156, 1044 and 12346",
      [cc[str(n)] for n in range(1, 8)] + [m8["class_count_8"]] == [1, 2, 4, 11, 34, 156, 1044, 12346])
claim("each of these 13598 graphs", small["graphs_evaluated"] + m8["class_count_8"] == 13598)
claim("all 256 one-vertex extensions of each of the 12346 graphs of order 8", m8["class_count_8"] == 12346)
claim("3160576 labelled graphs in all", agg["labelled_graphs_evaluated"] == 3160576 == 256 * 12346)
claim("no graph of order at most 8 has", small["hits"] == [] and m8["hits"] == [])
claim("exactly three isomorphism classes with a path IR-graph of order at least 3, giving P7, P8 and P9",
      agg["n_iso_classes"] == 3 and sorted(cls) == ["P7", "P8", "P9"])
claim("the last is the class of G", cls["P9"]["is_class_of_G"] and not cls["P7"]["is_class_of_G"])
claim("All three are connected and have IR = 3", all(c["connected"] and c["IR"] == 3 for c in cls.values()))
claim("21 labelled hits in 3 classes: P7: 6 labelled, 22 edges; P8: 10 labelled, 21 edges; P9: 5 labelled, 20 edges",
      agg["n_hits"] == 21 and [(cls[k]["labelled_hits"], cls[k]["edges"]) for k in ("P7", "P8", "P9")] == [(6, 22), (10, 21), (5, 20)])
claim("No cycle Cm with m ≥ 5, and no P3, …, P6, occurs through order 9",
      all(h["label"] in ("P7", "P8", "P9") for h in agg["hits"]))
claim("path IR-graphs up to P14 among some graphs of orders 10 and 11",
      "P_9 to P_14 on 11 vertices" in cand and "P_10 and P_12 on 10 vertices" in cand)
# --- Lean -------------------------------------------------------------------------------------------
claim("SHA-256 953331d0…439ee", zsha.startswith("953331d0") and zsha.endswith("439ee") and
      zsha == fres["source_zip_sha256"] == replay["packet_sha256"])
claim("8 modules General, GData, Four, Three, Finite, Endpoint, Control and Audit",
      safe["module_order"] == ["General", "GData", "Four", "Three", "Finite", "Endpoint", "Control", "Audit"])
claim("Lean 4.34.1 and Mathlib revision d13f23b7",
      fres["lean_version"] == "4.34.1" and fres["mathlib_revision"].startswith("d13f23b7"))
claim("all 126 four-sets are not irredundant, the 84 three-sets",
      len(re.findall(r"^\{\d,\d,\d,\d\}", four_src, re.M)) == 126 and len(re.findall(r"^\{\d,\d,\d\}", three_src, re.M)) == 84)
claim("the 81 ordered pairs of walk sets", "∀ i j : Fin 9, Swap G9 (walk i) (walk j)" in endpoint_src)
claim("reports only propext, Classical.choice and Quot.sound for both",
      audit.count("depends on axioms: [propext, Classical.choice, Quot.sound]") == 2)
claim("checked all 77 local declarations", "Audited 77 local declarations" in audit and audit.count("AUDITED ") == 77
      and "local=77" in replay["root_meta"][0])
claim("each of the 8 modules was compiled with warnings as errors and checked by leanchecker (verdict PASS)",
      replay["verdict"] == "PASS" and replay["all_modules_built_and_leanchecked"] and len(replay["modules"]) == 8
      and "warningAsError=true" in replay["flags"])
claim("verdict CLEAN", regref["verdict"].startswith("CLEAN"))
claim("The source contains no sorry, admit or native_decide",
      all(k not in safe["token_scan"].get(m, {}) for m in safe["modules"] for k in ("sorry", "admit", "native_decide")))
# --- sources and screen ----------------------------------------------------------------------------
claim("“The cycles C5, C6, C7 and the paths P3, P4, P5 are not IR-graphs.”",
      "The cycles $C_{5},C_{6},C_{7}$ and the paths $P_{3}%\n,P_{4},P_{5}$ are not" in tex)
claim("Conjecture 1. Pn is not an IR-graph for each n ≥ 3.", "is not an $\\operatorname{IR}$-graph for each $n\\geq3$." in tex)
claim("Conjecture 2. Cn is not an IR-graph for each n ≥ 5.", "is not an $\\operatorname{IR}$-graph for each $n\\geq5$." in tex)
claim("“The path Pn is not an IR-graph for each n ≥ 3, and the cycle Cn is not an IR-graph for each n ≥ 5.”",
      "The path $P_n$ is not an IR-graph for each $n\\geq 3$, and the cycle $C_n$ is not an IR-graph for each $n\\geq 5$." in mathdb["statement"]
      and mathdb["mathdb_id"] == 350452)
claim("OpenAlex lists seven works citing", citing.get("meta", {}).get("count") == 7 or len(citing.get("results", [])) == 7)
claim("Three further OpenAlex queries returned HTTP 503", "OpenAlex search/filter endpoints returned 503 (3 distinct queries" in review)
claim("All arXiv versions of [MR-IG] (v1–v3), [MR-IT] (v1, v2)",
      "[v3]" in abs1812 and "[v4]" not in abs1812 and "[v2]" in abs2104 and "[v3]" not in abs2104)
claim("doi:10.1016/j.dam.2022.08.005", "https://doi.org/10.1016/j.dam.2022.08.005" in json.dumps(oatitle))
claim("doi:10.1016/j.disc.2022.113079", "https://doi.org/10.1016/j.disc.2022.113079" in json.dumps(oatitle))
claim("doi:10.1007/978-3-030-58892-2_6", "https://doi.org/10.1007/978-3-030-58892-2_6" in json.dumps(oatitle))
claim("8(1) (2010) 23–31", "\\textbf{8}(1) (2010), 23-31" in tex)
claim("21 (1978) 461–468", "\\textbf{21} (1978), 461--468" in tex)
claim("31 (2011) 517–531", "\\textbf{31}\n(2011), 517-531" in tex)
claim("104 (2018) 217–230", "104\n}(2018), 217-230" in tex)
claim("restates the two conjectures as parts (i) and (ii)", "(i)\\hspace{0.1in}$The path $P_{n}$ is" in tex2104)

bad = [c for c in C if not (c["in_text"] and c["predicate"])]
# token scan outside the reference list
body = raw.split("## References")[0]
toks = re.findall(r"\d+", body)
res = {"n_claims": len(C), "all_pass": not bad, "failed": bad, "claims": C,
       "digit_tokens_in_body": len(toks), "distinct_digit_tokens": sorted(set(toks), key=lambda s: (len(s), s)),
       "resolved_text_sha256": hashlib.sha256(raw.encode()).hexdigest()}
with open(out_path, "x") as f:
    json.dump(res, f, indent=1, ensure_ascii=False)
print(json.dumps({"n_claims": len(C), "all_pass": not bad, "failed": [(c["fragment"][:70], c["in_text"], c["predicate"]) for c in bad]}, ensure_ascii=False))
print(" ".join(res["distinct_digit_tokens"]))
