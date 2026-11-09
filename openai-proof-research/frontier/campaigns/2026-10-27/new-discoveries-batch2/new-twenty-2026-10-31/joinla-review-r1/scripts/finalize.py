import pathlib,json,hashlib
r=pathlib.Path(__file__).resolve().parents[1]
p=r/'REVIEW.md';s=p.read_text()
s=s.replace('It proves a refutation, not the exact value 4.', 'This lower-bound argument alone proves the refutation. A separately verified four-weight certificate below establishes the exact value 4 in ordinary mathematics.')
s=s.replace('A bounded optional heuristic for four weights is recorded in scripts/four.py, logs/four-python.log, and outputs/four.json. Its restricted grouping and any failure carry no impossibility conclusion. No exact four-weight value is used.', '''My bounded independent heuristic found a four-weight certificate; scripts/check_four.py then checked it separately by reconstructing the source graph with named component vertices. All labels 1,…,30 occur once, every adjacent pair has different weights, and the exact palette is {45,49,84,99}. In the edge order (uv, ux₀, ux₁, vx₀, vx₁), the three pairs in the first component have labels (19,15,11,27,3), (22,2,21,10,17), (16,4,25,26,7), and the second component has (14,18,13,30,5), (20,24,1,6,23), (8,9,28,12,29). Every u has weight 45, every v weight 49, and the two null weights are 84 in the first component and 99 in the second. Thus the exact ordinary value is χ_la=4. The upper bound is not part of the replayed Lean theorem. See scripts/four.py, scripts/check_four.py, outputs/four.json, outputs/four-verified.json and their logs. This certificate is informative and is not needed for the formal refutation.''')
s=s.replace('Every Python, Lean, leanchecker and search process', 'Every Python, Lean, leanchecker and labeling-search process')
s=s.replace('the absence of an exact χ_la=4 result', 'the fact that the exact χ_la=4 upper bound is separately checked but not Lean-formalized')
p.write_text(s)
summary=dict(mathdb_id=365453,review_kind="independent adversarial and formal-fidelity review; not acceptance",
 date_utc="2026-11-04",overall="PROCEED TO ACCEPTANCE PACKAGING",accepted=False,credit=0,
 gates={
 "A":{"verdict":"PASS","reason":"Published Conjecture 4.1 and MathDB literal agree; r=s=1,m=2 is exactly the fixed graph.","references":["REVIEW.md:A","outputs/published.txt:917","replay/lean/Antimagic.lean:278"]},
 "B":{"verdict":"PASS","reason":"Complete independent proof and exhaustive necessary-weight enumeration rule out <=3; separately checked 4-weight certificate gives exact ordinary value 4.","references":["scripts/independent.py","outputs/independent.json","outputs/four-verified.json"]},
 "C":{"verdict":"PASS","reason":"Fresh strict build and explicit checker of both modules; graph, bijection, weights and <=3 endpoint faithful. Equivalent instantiated obstruction, not a general chi_la definition.","references":["replay/lean/Antimagic.lean:318","logs/Antimagic.log","logs/checker.log","logs/Audit.log","logs/checker-Audit.log"]},
 "D":{"verdict":"QUALIFIED_PASS","reason":"No prior refutation found in bounded primary-body/live screen; distinct from credited 354228. One inaccessible copies-paper body; registry path screens are not semantic exhaustive clearance.","references":["REVIEW.md:D","downloads/copies/receipt","downloads/preprint-citing/body","outputs/problems-screen.txt"]},
 "E":{"verdict":"QUALIFIED_PASS","reason":"Published universal conjecture refuted by complete mixed-role obstruction; not a tree-family parameter variant or source construction instance. Root decides significance and credit.","references":["REVIEW.md:E"]}},
 formal=dict(endpoint="R159.source_conjecture_4_1_counterexample",modules_built=["Antimagic","Audit"],modules_checked=["Antimagic","Audit"],local_declarations=97,transitive_declarations=6845,axioms=["propext","Classical.choice","Quot.sound"],local_flags=False,lean_memory_option="-M3500",warning_as_error=True,mathlib_rev="d13f23b723b8a846827a245b89c10fc7d3f11612",bridge_limitation="No general chi_la or family constructor is defined; endpoint is the equivalent fixed-instance existence obstruction. No mathematical gap identified.",upper_bound_lean_formalized=False),
 independent=json.loads((r/'outputs/independent.json').read_text()),
 four_weight_certificate=json.loads((r/'outputs/four-verified.json').read_text()),
 packet_sha256="a68ba4bde2e1f3dabacc336c30848ba0ed4a1f701e3df98e68d12eaf6bdd31aa",
 source_sha256="444d5df26217f4085e462dbdea61586ef9f52d8d33b51641e243c5a0f361a2c0",
 before_manifest_sha256=hashlib.sha256((r/'inputs-before.sha256').read_bytes()).hexdigest(),
 after_manifest_sha256=hashlib.sha256((r/'inputs-after.sha256').read_bytes()).hexdigest(),
 inputs_unchanged=(r/'inputs-before.sha256').read_bytes()==(r/'inputs-after.sha256').read_bytes(),
 limitations=["Bounded literature review; MDPI 403 not retried, body unread.","Registry filename screens are not exhaustive proof-body reviews.","Exact value 4 upper-bound certificate checked by independent code, not formalized."],
 resources=dict(cpus=[0,1],cpu_seconds=120,wall_seconds=140,rss_kib=6291456,rss_sample_seconds=0.1,malloc_arena_max=2,one_heavy_process=True),
 evidence=["REVIEW.md","inputs-before.sha256","inputs-after.sha256","family-inputs-before.sha256","scripts/","logs/","outputs/audit.tsv","downloads/"])
(r/'review.json').write_text(json.dumps(summary,indent=2)+'\n')
print("Wrote review.json; inputs unchanged:",summary["inputs_unchanged"])
