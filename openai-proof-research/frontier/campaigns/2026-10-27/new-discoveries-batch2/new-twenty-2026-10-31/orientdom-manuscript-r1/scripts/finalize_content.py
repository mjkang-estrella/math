from pathlib import Path
import json,hashlib,xml.etree.ElementTree as E,re
R=Path.cwd()
def sha(p): return hashlib.sha256(p.read_bytes()).hexdigest()
def put(p,d): (R/p).write_text(json.dumps(d,indent=2,ensure_ascii=False)+'\n')
v=json.loads((R/'recomputed/verification.json').read_text()); root=json.loads((R/'inputs/orientdom-root-ruling-r2.json').read_text()); raw=json.loads((R/'MathDB-360905.raw.jsonl').read_text()); src=(R/'paper.md').read_text()
proof='# Proof: orientable total domination interpolation\n\nDraft; AI-assisted. Finite simple graphs, incoming total domination.\n\n'+src.split('## 1. The problem and its domain\n\n')[1].split('Hansen, Lai')[0]+src.split('---PAGE---')[1]
(R/'PROOF.md').write_text(proof)
(R/'PRIOR-ART-LIMITATIONS.txt').write_text('\n\n'.join(root['gate_D_ruling'])+'\n')
table='| Order | Admissible labeled graphs | Valid orientations | Gaps |\n|---:|---:|---:|---:|\n'+'\n'.join(f"| {d['n']} | {d['graphs']:,} | {d['orientations']:,} | {d['gaps']} |" for d in v['orders'])
# FODT is the complete editable source; retain a resolved Markdown companion too.
ns={'text':'urn:oasis:names:tc:opendocument:xmlns:text:1.0','office':'urn:oasis:names:tc:opendocument:xmlns:office:1.0'}
xml=E.parse(R/'paper.fodt'); paragraphs=[''.join(p.itertext()) for p in xml.findall('.//office:body//text:p',ns)]
(R/'paper-expanded.md').write_text('\n\n'.join(paragraphs)+'\n')
qual=root['gate_D_ruling']; expanded=(R/'paper-expanded.md').read_text()
assert all(s in expanded for s in qual)
assert sha(R/'MathDB-360905.raw.jsonl')=='cf3072564d7631d411e42f3d16ceb44ee52e7a169e0bb1897e5b0ce730e496ad'
assert raw['first_stated_year']==2023
manifest=json.loads((R/'packet-safe-extraction/manifest.json').read_text()); replay=json.loads((R/'inputs/orientdom-parent-final-r1/replay-result.json').read_text())
assert manifest['all_local_declarations']==38 and '38 local declarations' in replay['root_meta']
assert manifest['lean']=='4.34.1' and replay['verdict']=='PASS'
assert '4 members' in replay['extraction']
# Recompute the disconnected scope correction directly from fresh per-graph data.
spectra=json.loads((R/'recomputed/spectra.json').read_text()); ds=[g for g in spectra['6']['graphs'] if not g['connected']]
assert len(ds)==10 and sum(g['orientations'] for g in ds)==40
assert all(g['spectrum']==[6] and g['edge_mask'].bit_count()==6 for g in ds)
checks=dict(status='PASS',mathematical_values='Fresh enumeration and all-subset cycle checks, scripts/recompute.py and aggregate.py.',disconnected_graphs=len(ds),extra_orientations=sum(g['orientations'] for g in ds),raw_sha256=sha(R/'MathDB-360905.raw.jsonl'),root_qualifications_exact=True,documentary_numbers=dict(lean_version=manifest['lean'],local_declarations=manifest['all_local_declarations'],packet_members=4),documentary_policy='Bibliographic dates, printed page/theorem labels, formal-run counts and version identifiers are source metadata, not recomputed theorems. Checked against frozen sources and receipts; no new Lean run.')
put('receipts/paper-values.json',checks)
# Every final page was inspected visually by the authoring agent after rendering.
images=sorted((R/'qa').glob('page-*.png')); assert len(images)==5
put('receipts/page-qa.json',dict(status='PASS',pages=5,pdf_sha256=sha(R/'paper.pdf'),method='Every final page rendered by pdftoppm at scale-to 1600 and visually inspected individually.',observations=['Page 1: title, draft/AI disclosure, definitions, exact conjectures and main theorem legible.','Page 2: both lemma proofs and induction complete, symbols legible, no clipping.','Page 3: cycle examples, enumeration table and scope reconciliation legible.','Page 4: formal mapping and trust limits fit together on one page.','Page 5: exact root qualifications and complete bibliography fit without clipping.'],images=[dict(path=str(p.relative_to(R)),sha256=sha(p)) for p in images],initial_revision='Initial six-page layout orphaned a trust-limit paragraph; tightened table/section spacing and re-rendered all final pages.'))
discrepancies=["arXiv v1 Conjecture 3.1 cites [10] Holley–Lai–Yue, not [8] Hansen–Lai–Yue; the 1999 Hansen–Lai–Yue scan independently prints the same unnumbered conjecture with rho_1/dom_1/DOM_1 notation.","MathDB first_stated_year 2023 records the preprint date, while the conjecture is printed in the preserved 1999 source.","Discovery enumerates connected graphs; review enumerates all graphs. At order 6 the difference is 10 disjoint pairs of triangles and 40 valid orientations. Both are freshly reproduced.","Original packet metadata says independent review PENDING. It predates the preserved completed review and subsequent root ruling; byte-identical packet retained.","domination1999.txt is essentially page breaks. The actual scan and saved page images, not that extraction, establish the printed conjecture.","Review's order-5 pair/set extension was capped (exit 137), not a completed confirmation; no such result is claimed."]
put('results.json',dict(mathdb_id=360905,title='Interpolation of orientable total domination by safe arc reversals',status='DRAFT manuscript and reproducible dossier complete; no acceptance asserted',pages=5,ai_assistance='OpenAI Codex; no human author or affiliation invented',theorem='Every finite simple graph admitting a valid orientation has an interval of attained total domination numbers.',accepted_credit=0,campaign_context='42/60 beyond 39, per task; root alone accepts',recomputation=v,discrepancies=discrepancies,prior_art_qualifications_exact=root['gate_D_ruling'],formal=dict(endpoint=replay['endpoint'],packet_sha256=sha(R/'Lean-packet.zip'),new_lean_run=False,historical_replay='PASS',registry='CLEAN within recorded scope',dependencies_rebuilt=False),artifacts=dict(paper='paper.pdf',editable_source='paper.fodt',source_template='paper.md',resolved_source='paper-expanded.md',proof='PROOF.md',full_dossier='full-dossier.zip',source_bundle='manuscript-source.zip',lean_packet='Lean-packet.zip',qa='qa/',receipts='receipts/',manifest='PAYLOAD-MANIFEST.json')))
summary='''# Draft manuscript and dossier: MathDB 360905

**Interpolation of orientable total domination by safe arc reversals** — five-page unpublished, AI-assisted draft. No human author or affiliation is asserted. The proof resolves the finite-simple-graph assertion, including disconnected admissible graphs. This lane awards zero accepted credit; root alone accepts. Task campaign context: 42/60 beyond 39.

Fresh isolated Python enumeration of all labeled simple graphs and orientations at orders 3–6: **PASS, no spectrum gaps**. Admissible graph counts: 1, 22, 603, 25,418. Valid orientation counts: 2, 122, 16,168, 5,545,708. Connected order-6 counts: 25,408 and 5,545,668. Cycle examples were recomputed by all-subset tests. Full per-graph spectra are in `recomputed/spectra.json`.

The Lean packet is byte-identical to the supplied packet (SHA-256 `3d9361bef2cc188b191519cd9718e4d983ccbe6b17df8dec6448dcf5228ab1d6`). A safe extraction test passes. Historical review/root compile, kernel and audit receipts are preserved; no Lean, lake, leanchecker or solver was run here. Cached upstream oleans remain a trust limit.

All five final PDF pages were rendered and visually inspected. Page images and a hash-bound QA receipt are included. The initial ReportLab import failed because it is unavailable locally; the final editable FODT and PDF were generated offline with Python standard-library XML and LibreOffice. Failure receipts are retained. No installation was performed.

## Discrepancies and qualifications

'''+ '\n\n'.join('- '+d for d in discrepancies)+'''

The root ruling's qualified prior-art language is reproduced exactly in the paper and `PRIOR-ART-LIMITATIONS.txt`: the print-only 1996 proof and DAM 2026 version of record remain unread; citing-work coverage is bounded. Earlier HOLD recommendations are not rewritten as independent clearance. No priority claim is made.

## Deliverables

- `paper.pdf`, `paper.fodt`, `paper.md`, `paper-expanded.md`, `PROOF.md`.
- `results.json`, `REPRODUCE.md`, scripts and all per-graph recomputation outputs.
- `MathDB-360905.raw.jsonl` and hash receipt; all 646 frozen inputs and original source acquisition receipts in `inputs/`.
- `Lean-packet.zip`, safe extraction, `manuscript-source.zip`, `full-dossier.zip`.
- `inputs-before.json`, `inputs-after.json`, `PAYLOAD-MANIFEST.json`, `ARTIFACTS.sha256`, `qa/`, `receipts/`.

No network, git, delegation, browser, publication, upload or external messaging was used. All writes are lane-local. Foreground resource wrappers record command, affinity, CPU/wall limits, sampled process-group RSS and exit status. No running task remains at handback.
'''
(R/'SUMMARY.md').write_text(summary)
print('Wrote proof, resolved source, summary, results and QA/value receipts')
