from pathlib import Path
import json,hashlib,os
O=Path.cwd();B=O.parent
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
# Remove the obsolete seventh rendering from the superseded layout.
(O/'qa/page-7.png').unlink(missing_ok=True)
before=json.loads((O/'inputs-before.json').read_text());after={k:sha(B/k) for k in before}
(O/'inputs-after.json').write_text(json.dumps(after,indent=2)+'\n');assert before==after
(O/'receipts/input-integrity.json').write_text(json.dumps(dict(status='PASS',files=len(after),before_sha256=sha(O/'inputs-before.json'),after_sha256=sha(O/'inputs-after.json'),changed=[],scope='All regular files in frozen discovery, review, parent-final lanes plus root ruling; no inputs modified'),indent=2)+'\n')
qa=dict(status='PASS',pdf_sha256=sha(O/'paper.pdf'),pages=6,method='Each final page rendered by pdftoppm at scale-to 1250 and individually visually inspected using view_image',checks=['All six pages individually inspected','Headings separated from paragraphs; no template tokens remain','Complete decomposition and stage weights legible','All 24 residual-edge rows present','Lower-bound proof and conclusion on page 3','No clipping, overlap, missing glyphs or orphan pages','Consistent draft footer and page numbering'],images={f'qa/page-{i}.png':sha(O/f'qa/page-{i}.png') for i in range(1,7)},iterations='Initial formatting and one orphan overflow page corrected before final inspection')
(O/'receipts/visual-qa.json').write_text(json.dumps(qa,indent=2)+'\n')
(O/'REPRODUCE.md').write_text('''# Offline reproduction (no Lean execution in this preparation)

Run from this dossier directory. Python 3 standard library suffices for arithmetic and archive inspection. No solver, network, account or browser is needed. All writes must remain here.

```
python3 -B cap.py arithmetic-reproduce python3 -B verify.py
```

This reconstructs Cartesian adjacency and checks all four certificates, including complete partitions, nonempty disjoint matchings, selected sums exactly 1, and strict negativity on every other residual edge. Output: receipts/arithmetic.json. The cap receipt uses a different name so it cannot overwrite the arithmetic data.

The exact raw line is raw/366974.jsonl; raw/366974.sha256 binds every byte, including its newline. Original discovery results are excerpted under evidence/discovery/results-366974.json; their old unread-thesis gap is superseded by evidence/review/REVIEW.md and evidence/root/ruling.json. No historical receipt has been rewritten to appear current.

The original lean-packet.tar.gz is reused byte-identically. receipts/safe-extraction.json records actual extraction into safe-extracted/: all member names were checked for absolute paths and parent traversal; only regular files/directories were accepted, with every link/device rejected. Python tarfile.extractall(filter='data') was used. The extracted TorusPMD.lean equals the frozen source byte for byte. verify.py repeats the packet hash and member-policy checks without executing any archive content. prepare.py records how source copies and the extraction were made; it is a one-time preparation script and expects the original sibling lanes and a fresh extraction directory.

For PDF generation use Python with ReportLab and DejaVu fonts:

```
python3 -B cap.py pdf-reproduce /home/mj-kang/.cache/codex-runtimes/codex-primary-runtime/dependencies/python/bin/python3 -B build_pdf.py
python3 -B cap.py render-reproduce pdftoppm -scale-to 1250 -png paper.pdf qa/page
```

build_pdf.py uses paper.md as its narrative template and frozen JSON certificate data for tables; paper-source.md is the fully expanded readable source. PROOF.md includes the same complete proof. The font directory is set in build_pdf.py to the available local runtime; adjust that path on another host. PDF creation metadata may change, so a regenerated PDF need not have identical bytes. Check the final page count (6) and visually inspect every regenerated page. No package installation or downloads occurred in this preparation. The default Python lacked ReportLab; an existing local runtime supplied it.

The cap wrapper sets at most two CPUs, MALLOC_ARENA_MAX=2, CPU 120 seconds, wall 140 seconds, address-space 6 GiB and sampled aggregate process-group RSS 6 GiB. One heavy process ran at a time. Small read-only inventory and file-authoring commands were lightweight and completed synchronously. Resource receipts include commands, affinity, sampled peak RSS and exit status.

No Lean, lake or leanchecker was run. For the previously completed Lean checks, consult evidence/root/replay-result.json and the original logs; they report Lean 4.34.1 and mathlib revision d13f23b723b8a846827a245b89c10fc7d3f11612. Imported packages were not rebuilt here. The endpoint is TorusPMD.refutes_conjecture_4_7. The exact-value lower bound remains a prose theorem, and extra certificates have no additional formal endpoint.

inputs-before.json and inputs-after.json bind all 314 frozen input files, with equality recorded in receipts/input-integrity.json. They are relative to the original parent campaign directory; only selected source copies are included in this dossier. SHA256SUMS binds the deliverable payload. Verify it with `sha256sum -c SHA256SUMS`. Full-dossier ZIP member paths are relative and its decompressed contents are checked byte-for-byte against the payload. ARCHIVES.sha256 binds both ZIPs and the original tar.gz externally. Archive creation and its resource receipt are excluded from the embedded self-manifest as explained in receipts/package-check.json.

This is a draft with modest significance and bounded prior-art review, not a priority certificate. Accepted credit is zero. Root reads the manuscript and decides.
''')
(O/'SUMMARY.md').write_text('''# MathDB 366974: manuscript and reproducible dossier

DRAFT, AI-assisted; zero accepted credit. Root alone reads and adjudicates.

The six-page paper proves pmd(C_3 □ C_4) = 5 by a fully printed five-part partition, stage weights, all residual edge sums and the regular-graph lower bound (r ≥ 2). It refutes the explicitly listed (3,4) case of arXiv:2502.02826v1, Conjecture 4.7. Supporting (3,5), (3,6), (3,7) certificates are the same family, with no additional credit or Lean endpoint.

Deliverables: paper.pdf; paper-source.md (expanded source); paper.md and build_pdf.py (build inputs); PROOF.md; REPRODUCE.md; results.json; manuscript.zip; full-dossier.zip; original byte-identical lean-packet.tar.gz; SHA256SUMS; ARCHIVES.sha256; receipts/; qa/page-1.png through page-6.png; raw/366974.jsonl with hash; selected source copies and original review/root receipts under evidence/.

Validation: all four certificates independently rechecked with exact integers; safe extraction and byte identity passed; all six final PDF pages rendered and visually inspected; all 314 frozen input hashes unchanged. No Lean/lake/leanchecker executions, child agents, git operations, browser, external requests, messages, uploads or shared edits. Resource-capped heavy commands completed; no jobs left running.

Historical replay PASS is cited from the root receipt, not newly performed. The Lean endpoint proves the upper bound and universal refutation; the manuscript proves the exact-value lower bound. Prior-art findings remain bounded, with the alternative Genova thesis copy and TLS/access limits disclosed. No priority claim. Remaining gate: root paper read and acceptance decision.
''')
result=dict(mathdb_id=366974,status='draft_manuscript_and_dossier_complete_pending_root_read',accepted=False,discovery_credit=0,claim='pmd(C_3 □ C_4) = 5; Conjecture 4.7 of arXiv:2502.02826v1 is false',lean_endpoint='TorusPMD.refutes_conjecture_4_7',lean_executed_this_task=False,formal_scope='upper bound 5 and negation of full universal conjecture; lower bound proved in prose',packet_sha256=sha(O/'lean-packet.tar.gz'),paper='paper.pdf',source='paper-source.md',pages=6,extra_cases=[[3,5],[3,6],[3,7]],extra_credit=0,validation=dict(arithmetic='PASS',safe_extraction='PASS',visual_qa='PASS all 6 pages',frozen_inputs='PASS 314 unchanged',historical_root_replay='PASS per evidence/root/replay-result.json'),novelty='bounded qualified prior-art finding; no priority claim',significance='modest finite-search counterexample',remaining_gate='root manuscript read and acceptance adjudication')
(O/'results.json').write_text(json.dumps(result,indent=2)+'\n')
print('Final records written; 314 frozen inputs unchanged; six-page visual QA recorded.')
