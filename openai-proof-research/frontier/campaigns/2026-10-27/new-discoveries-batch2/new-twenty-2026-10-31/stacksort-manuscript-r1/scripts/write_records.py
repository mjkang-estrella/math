#!/usr/bin/env python3
"""Write raw/345545.provenance.json, lean/ZIP-RECORD.json and gate-E-map.json (run from lane root)."""
import json, hashlib
from pathlib import Path
sha = lambda p: hashlib.sha256(Path(p).read_bytes()).hexdigest()
raw = Path('raw/345545.jsonl'); b = raw.read_bytes(); rec = json.loads(b)
r133 = json.load(open('../expanded-corpus-r133/results.json'))
prov = {"file": "raw/345545.jsonl", "sha256": sha(raw), "bytes": len(b), "lines": b.count(b'\n') + (0 if b.endswith(b'\n') else 1),
        "copied_from": "../expanded-corpus-r133/raw/345545.jsonl", "source_sha256": sha('../expanded-corpus-r133/raw/345545.jsonl'),
        "r133_results_provenance_raw_sha256": r133['345545']['provenance']['raw_sha256'],
        "mathdb_id": rec["mathdb_id"], "uuid": rec["uuid"], "canonical_url": rec["canonical_url"],
        "retrieval_source": rec["retrieval_source"], "lastmod": rec["lastmod"], "status_in_record": rec["status"],
        "solution_count": rec["solution_count"],
        "paraphrase_defect": "statement says 'maximum fiber size'; source Definition 1.1 is the average multiplicity",
        "note": "exact bytes preserved; no fresh MathDB access by this lane"}
prov["byte_identical_to_source"] = prov["sha256"] == prov["source_sha256"] == prov["r133_results_provenance_raw_sha256"]
Path('raw/345545.provenance.json').write_text(json.dumps(prov, indent=1, ensure_ascii=False) + '\n')
z = 'lean/stacksort-source6.zip'
zr = {"file": z, "sha256": sha(z), "expected_sha256": "9b734e2fe521651fd33bbf92bdf05f1b542a6aeb82f90d2cd1e13399d6cf5c2f",
      "copied_from": "../stacksort-formal-r6/stacksort-source6.zip", "source_sha256": sha('../stacksort-formal-r6/stacksort-source6.zip'),
      "bytes": Path(z).stat().st_size, "lean_modules": 92, "other_files": 8, "endpoint_module": "src/StackSortFinal6.lean",
      "namespace": "StackSort.Round6",
      "endpoints": ["mathdb_345545", "limit_ge", "nonvacuity", "subsequence_companion", "mathdb_345545_max", "max_companion"],
      "lean_version_recorded_by_r6": "4.34.1", "mathlib_packages_pin_recorded_by_r6": "d13f23b723b8a846827a245b89c10fc7d3f11612",
      "safe_extraction_report": "safe-extraction-report.json", "lean_executed_in_this_lane": False}
zr["byte_identical"] = zr["sha256"] == zr["source_sha256"] == zr["expected_sha256"]
Path('lean/ZIP-RECORD.json').write_text(json.dumps(zr, indent=1) + '\n')
gate = {"fidelity_review": "../stacksort-fidelity-r1/REVIEW.md; see hashes/live-read-*.sha256 for the versions read",
        "items": {
 "E.1 average-multiplicity refutation; >=1.73 for every possible limit; frequent exceedance; indices 131*2^k-1; existence attributed to source Thm 2.5; no stronger numeric bound advertised as formal":
   "paper Abstract, Thm 1.1, Thm 1.2 (labelled not formalised), proof of Thm 1.1 (1.73006 marked ordinary), Sec. 8 fidelity points, trust limits (i), (iv)",
 "E.2 exact top-max recursion, multiplicities, shuffle coefficients, empty-domain conventions, seeds P1..P20, lower recursion, certificate; clipped formal table; P1..P82 separate":
   "paper Sec. 4 (Lemmas 4.1-4.4, Thm 4.5, X(0,0,0)=1, scope paragraph), Lemma 5.5, Table 1, Sec. 7, trust limits (i), (iii)",
 "E.3 both readings; MathDB wording defective; no credit":
   "paper Sec. 2 'The MathDB record', Sec. 8 endpoint list and Table 3 last row; STATEMENT-CORRESPONDENCE.md",
 "E.4 version history v1/v2 (1.6,1.8), v3/v4, EJC Conjecture 23":
   "paper Sec. 2 'Version history' (cached v1-v4 and EJC copies from the review lane, receipts in sources/review-dl-r1)",
 "E.5 reviewer observation: P1..P13 suffice (base 910); recursion not essential":
   "paper Remark 5.6; PROOF.md Sec. 5; evidence/math-check.json first_a_passing_1_73_by_seed_depth",
 "E.6 compilation, checker scope, axioms, source scan, diagnostics separately; P5/P6 direct limit not a proof hole; candidate bounds distinct":
   "paper Sec. 8 'Audits and controls' bullet list, 'Checks in this lane', trust limits (ii)",
 "E.7 access limits; frozen local sources only; no exhaustive novelty":
   "paper Sec. 9 (bounded review search, root registry path screen, no fresh access); SUMMARY.md"},
        "unresolved": []}
Path('gate-E-map.json').write_text(json.dumps(gate, indent=1, ensure_ascii=False) + '\n')
print(prov['sha256'], prov['byte_identical_to_source'], zr['byte_identical'])
