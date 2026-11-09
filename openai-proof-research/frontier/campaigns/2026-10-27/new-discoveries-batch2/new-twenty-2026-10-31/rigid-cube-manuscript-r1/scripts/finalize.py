from pathlib import Path
import json,hashlib
D=Path(__file__).resolve().parents[1]
bind=json.loads((D/'frozen-before.json').read_text());bad=[p for p,h in bind.items() if not Path(p).is_file() or hashlib.sha256(Path(p).read_bytes()).hexdigest()!=h]
assert not bad,bad
(D/'frozen-after.json').write_text(json.dumps(dict(status='PASS',files=len(bind),changed=bad),indent=2)+'\n')
for n in ['Cube','Signed']:
 assert (D/f'formal/{n}.lean').read_bytes()==(D.parent/f'expanded-corpus-r59/formal/{n}.lean').read_bytes()
r=json.loads((D/'fresh-replay/receipts/replay.json').read_text());assert r['status']=='PASS'
qa=json.loads((D/'qa/inspection.json').read_text());assert qa['pages']==6 and qa['status']=='PASS'
result=dict(status='DRAFT_COMPLETE',gate1='PASS',gate2='PASS_DRAFT_ARTIFACTS',accepted_credit=0,campaign='7/20 beyond 39 unchanged; root alone accepts',endpoint='MathDB364205.literal_source_refutation',fresh_archive_replay='PASS',frozen_bindings='311 unchanged',proof_modules_byte_identical=True,manuscript_pages=6,novelty='QUALIFIED_PASS inherited bounded source review, not priority',trust_limits=['Pinned prebuilt external oleans and compiler trusted','No upstream rebuild/source-to-olean attestation','No exact optimum, minimality, family or priority claim'],operational_exception='Initial relative PDF marker invocation failed; installed helper later resolved and used before final regeneration. Initial build preceded the successful marker; logs retained.',no_running_jobs='All launched tasks completed; driver kills guarded jobs on cap; final process check recorded separately')
(D/'results.json').write_text(json.dumps(result,indent=2)+'\n')
(D/'SUMMARY.md').write_text('''# MathDB 364205: two gates, DRAFT dossier

Gate 1: **PASS** independent strict technical audit, reported separately in TECHNICAL-REVIEW.md and technical-review.json. All five original packet modules and two positive reviewer supplements strictly rebuild; separate leanchecker passes for each. All 33 mathematical declarations including generated auxiliaries have actual bodies, safe/nonpartial flags and only permitted transitive axioms. Two explicitly scoped negative controls fail as intended. The endpoint matches the signed primary-source conjecture.

Gate 2: **DRAFT complete**. draft.pdf is a six-page manuscript with editable paper.json and scripts/build_paper.py. It gives exact definitions, the 34-point encoding, an ordinary bounded exhaustive proof, a Lean correspondence table, explicit prior-art comparisons, references and bounded limits. All six pages were rendered and inspected; qa/inspection.json records the review. No human authorship or affiliation is fabricated; AI assistance and draft status are explicit.

source-only.zip contains proof and manuscript sources plus a portable replay driver. full-dossier.zip contains the draft, sources, raw MathDB record and hash, primary bodies/receipts, certificates, audit reports, logs, pins, manifests, and fresh replay evidence. A safe fresh extraction of source-only.zip rebuilt successfully. REPRODUCE.md explains pins, trust boundaries, caps and cleanup. All 311 frozen input file bindings remain unchanged. Cube.lean and Signed.lean are byte-identical to the author originals.

Limitations: prebuilt external oleans/compiler are trusted, not rebuilt or independently source-attested. Novelty/significance retain the prior review's qualified status; no optimum, minimality, infinite family or priority is claimed. The first PDF marker invocation used a wrong relative path. The installed helper was later resolved and used before final regeneration; the initial build preceded the successful marker, a procedural deviation retained in the logs. PDF rendering/inspection succeeded. Reviewer-harness development failures and corrected reviewer-only examples are documented separately from the author theorem.

Zero accepted credit. Campaign count 7/20 beyond 39 unchanged. Root alone accepts. No git, children, publication, upload, external messages, browser, cache mutation, shared-ledger or other-lane writes were used. No running jobs remain at handback.
''')
print('Final bindings, replay, byte identity and six-page QA PASS')
