from pathlib import Path
import hashlib,json,shutil
r=Path(__file__).resolve().parent.parent
paper=(r/'paper.md').read_text()
(r/'PROOF.md').write_text('# Proof dossier: MathDB 355217\n\nDRAFT; AI-assisted. Zero accepted credit. The finite graph result is formalized in the byte-identical packet; the structural results below are ordinary mathematical proofs.\n\n'+paper[paper.index('## 2.'):paper.index('## 5.')].replace('===PAGE===','')+'\n\n'+paper[paper.index('## 6.'):paper.index('## References')].replace('===PAGE===','').replace('FORMAL_TABLE','See paper.pdf, Section 7, and evidence/middle-formal-r1/STATEMENT-CORRESPONDENCE.md for the correspondence table.')+'\n')
(r/'gate-E.md').write_text('''# Fidelity gate E disposition (manuscript integration, not acceptance)

The frozen review is evidence/middle-fidelity-r1/REVIEW.md, Section E. All eight integration conditions are addressed:

1. Paper Sections 1–3: exact source definitions and conjecture; connected 11-edge G8, attained values, both witnesses, four-case original-graph bound and middle counting.
2. Sections 2 and 6: separate conventions; connected universal negations; edgeless observation uncredited; no convention-B attained minimum and sInf totalization explained.
3. Sections 3–4: even n ≥ 2 connected characterization, disjoint coverage and path projection; a,b ≥ 1 family, four cases, explicit upper witness and matching. Ordinary mathematics, outside Lean packet.
4. Section 5: computation up to isomorphism, all and connected counts, exact search coverage, scripts/data/logs, 378 crosschecks. Classification was not rerun in this lane and is not a Lean theorem.
5. Section 6: K2,2 middle minimum 3 (explicit upper witness and lower bound); friendship original minimum k for k ≥ 2. Both uncredited, with proofs.
6. Abstract and Sections 3, 4, 6: specialized modest significance, source counting/matching ingredients, decisive separate G8 bound, friendship near-tightness and source standing; no reversal or priority claim.
7. Sections 5 and 7: pinned versions and archive hash, IsLeast table, audits and controls, independent finite regression, resource discipline. Root replay receipt explicitly distinguished and cited as PASS; this lane did not run Lean.
8. Section 6: dated cached arXiv/OpenAlex evidence, path-only registry screen and access exclusions. No fresh network or worldwide novelty clearance. Current final endpoint names replace obsolete uncompiled draft status; obsolete discovery notes are retained only as labeled historical evidence.

Root still reads the complete manuscript and decides. This file is a disposition checklist, not an independent review or acceptance.
''')
shutil.copyfile(r/'evidence/expanded-corpus-r139/raw/355217.jsonl',r/'mathdb-355217.jsonl')
rawhash=hashlib.sha256((r/'mathdb-355217.jsonl').read_bytes()).hexdigest()
(r/'mathdb-355217.sha256').write_text(rawhash+'  mathdb-355217.jsonl\n')
(r/'REPRODUCE.md').write_text('''# Reproduction and artifact map

DRAFT, AI-assisted; zero accepted credit. All paths below are relative to this dossier. Work in an isolated writable copy under an authorized directory. This lane executed no Lean, lake or leanchecker and made no network requests.

- paper.md is the complete editable prose source, with explicit page divisions. scripts/build.py converts it to the portable flat OpenDocument source paper.fodt. paper.pdf is the eight-page exported draft. LibreOffice 26.8.2.2 was used because reportlab is not installed; the failed import receipt is preserved. No dependencies were installed.
- Rebuild source: `python3 scripts/run.py build-source python3 -I scripts/build.py`.
- Export: `python3 scripts/run.py render libreoffice -env:UserInstallation=file:///ABSOLUTE/AUTHORIZED/DOSSIER/cache/lo --headless --convert-to pdf --outdir . paper.fodt`. Replace the profile URL with a path within your authorized copy. No browser or server is required. Font: installed Noto Serif. LibreOffice may embed timestamps; reproduced PDFs need not have identical bytes.
- Render: `python3 scripts/run.py qa pdftoppm -scale-to 1250 -png paper.pdf qa/page`. Inspect every page. qa/ contains all final page PNGs and text extraction; receipts/pdf-qa.json binds the inspected final PDF and images.
- PROOF.md restates the proofs and scope; gate-E.md maps all eight fidelity conditions.
- mathdb-355217.jsonl is the exact cached raw line, including its terminal newline; mathdb-355217.sha256 binds its bytes. Do not treat its historical open status as present-day novelty evidence.
- evidence/ retains byte-identical read-only copies under original lane names, including source PDFs/text/receipts, mathematical/fidelity reviews, formal audit and results, root ruling, root replay and registry refresh. receipts/copied-inputs.json maps originals to copies and hashes. Historical obsolete discovery draft descriptions are provenance, not the current formal status.
- scripts/collect.py documents collection from the original sibling lanes; it requires that original layout. It was run once. No shared ledger is included or changed.

## Safe packet verification without Lean

middle-source.zip must have SHA-256 5a3e8ac8153651c55942d8f1288b50dd0c578b089c02d01c353b750b2c5bb62b. It is reused byte-identically. scripts/check.py rejects absolute paths, parent traversal, backslashes, duplicate names and symlinks, extracts into a newly created safe-extraction/, and compares every member byte-for-byte. It then independently builds G8 and its literal middle graph and enumerates subsets through the first feasible cardinality under both conventions. Run `python3 scripts/run.py checks python3 -I scripts/check.py` in a fresh copy without safe-extraction/. It deliberately refuses an existing extraction directory. No archive script is executed. Receipts record all 18 members, graph sizes, values and minimizing sets.

## Historical Lean replay (not run in this lane)

The archive contains the authentic source and its scripts. See evidence/middle-formal-r1/REPRODUCE.md for the original exact local dependency paths and replay command. Lean is 4.34.1; mathlib commit d13f23b723b8a846827a245b89c10fc7d3f11612. Replay requires those already installed read-only dependencies; this is not a hermetic dependency distribution. Compile serially with -j1 -M3500 -DwarningAsError=true and explicit-module leanchecker for MiddleBase, MiddleSmall, MiddleWitness, MiddleFinal and MiddleAudit. The root receipt evidence/middle-parent-final-r1/replay-result.json reports all passes, three expected negative failures, regression and allowed axioms. Fidelity review logs are independent bounded checks. Neither receipt rebuilds upstream mathlib from source.

## Reproducing the classification (not rerun here)

Read evidence/middle-review-r1/scripts/{gen.py,search.py,crosscheck.py,mocd.py} and their scripts/run.sh. Original commands and outcomes are retained in evidence/middle-review-r1/logs/. Class representatives are data/all1.txt through all8.txt. The review scripts resolve data paths against their lane, so use a fresh writable copy of that subtree and preserve originals. The discovery generator is evidence/expanded-corpus-r139/scripts/graphgen.py; its witness scripts are in work355217/. Family and characterization are proved in the paper; classification is computation only.

## Integrity and resource limits

frozen-inputs-before.json and frozen-inputs-after.json bind every file recursively in the five input lanes plus the root ruling. receipts/frozen-inputs.json reports byte identity. MANIFEST.sha256 and MANIFEST.json bind every distributed payload file; they exclude themselves and the archive checksum files to avoid self-reference. Cache/profile/tmp files and safe-extraction/ duplicates are intentionally omitted from the full-dossier ZIP; the extraction receipt and original source ZIP are included. The packaging supervisor receipt is written after packaging and is a sidecar; it and ARCHIVES.sha256 are outside the payload manifest. The ZIP's member list and byte hashes are checked against the manifest before completion.

scripts/run.py enforces two available CPUs, per-process CPU 120 s, wall 140 s, sampled process-group RSS 6 GiB, MALLOC_ARENA_MAX=2 and lane-local temporary/cache directories. Heavy operations run serially and are waited on. Shell setup and read-only inspection are lightweight. receipts/ includes successful and failed attempts; fonts.json records a failed isolated reportlab import. No jobs remain at handback. No acceptance is implied by a passed integrity check.
''')
qa=[]
for p in sorted((r/'qa').glob('page-*.png')):qa.append({'page':int(p.stem.split('-')[-1]),'path':str(p.relative_to(r)),'sha256':hashlib.sha256(p.read_bytes()).hexdigest(),'visual_inspection':'PASS: readable text and symbols, no clipping or overlaps; headings, table, references and page numbering checked'})
assert len(qa)==8
(r/'receipts/pdf-qa.json').write_text(json.dumps({'pdf_sha256':hashlib.sha256((r/'paper.pdf').read_bytes()).hexdigest(),'pages':8,'method':'pdftoppm PNG render, every page visually inspected via view_image after final export','page_checks':qa,'layout':'PASS','source':'paper.md and paper.fodt','pdf_generator':'LibreOffice 26.8.2.2'},indent=2)+'\n')
before=json.loads((r/'frozen-inputs-before.json').read_text());after={p:hashlib.sha256(Path(p).read_bytes()).hexdigest() for p in before}
(r/'frozen-inputs-after.json').write_text(json.dumps(after,indent=2)+'\n')
changed=[p for p in before if before[p]!=after[p]];assert not changed,changed
(r/'receipts/frozen-inputs.json').write_text(json.dumps({'files':len(before),'unchanged':True,'changed':changed,'before_manifest_sha256':hashlib.sha256((r/'frozen-inputs-before.json').read_bytes()).hexdigest(),'after_manifest_sha256':hashlib.sha256((r/'frozen-inputs-after.json').read_bytes()).hexdigest()},indent=2)+'\n')
result={'mathdb_id':355217,'status':'DRAFT_MANUSCRIPT_AND_DOSSIER_FOR_ROOT_REVIEW','self_accepted':False,'credit':0,'decision_owner':'root','pdf_pages':8,'gate_E_conditions_addressed':list(range(1,9)),'lean_run_in_this_lane':False,'source_zip_sha256':'5a3e8ac8153651c55942d8f1288b50dd0c578b089c02d01c353b750b2c5bb62b','source_zip_byte_identical':True,'safe_extraction':'PASS; 18 members; no execution','witness_check':'PASS both conventions, values 4 and 4; 8 and 2 minimizers','full_classification_rerun':False,'root_replay':'PASS per copied replay-result.json, not rerun','frozen_input_count':len(before),'frozen_inputs_unchanged':True,'pdf_visual_QA':'PASS every final page','raw_line_sha256':rawhash,'compliance':{'child_agents':False,'network':False,'browser':False,'git':False,'publication_upload_messages':False,'shared_ledger_edits':False,'other_lane_edits':False,'running_jobs_at_handback':False},'limitations':['Zero accepted credit; root decides','Family and characterization ordinary proofs, classification computation, all outside finite Lean packet','Bounded cached literature and registry evidence; no worldwide novelty clearance','Pinned upstream Lean/mathlib dependencies not bundled','Reportlab unavailable; used installed LibreOffice with lane-local profile'],'deliverables':['paper.pdf','paper.md','paper.fodt','PROOF.md','REPRODUCE.md','gate-E.md','middle-source.zip','middle-dossier.zip','MANIFEST.sha256','MANIFEST.json','ARCHIVES.sha256','receipts/']}
(r/'results.json').write_text(json.dumps(result,indent=2)+'\n')
(r/'SUMMARY.md').write_text('''# MathDB 355217: DRAFT manuscript and reproducible dossier

Zero accepted credit. Root reads the paper and decides. No self-acceptance, publication or upload.

The eight-page AI-assisted draft paper.pdf (editable paper.md and paper.fodt) proves the connected 11-edge G8 counterexample with both attained minima 4 under both conventions, the infinite equality family and the connected even-order perfect-matching characterization. It labels smallest-order uniqueness as computation, records the two uncredited source corrections, and states modest significance and bounded access limits. gate-E.md addresses all eight fidelity-review conditions.

The immutable Lean source-only ZIP is reused byte-identically at SHA-256 5a3e8ac8153651c55942d8f1288b50dd0c578b089c02d01c353b750b2c5bb62b. This lane safely extracted all 18 members and compared bytes, without running Lean, lake or leanchecker. Independent literal Python enumeration confirms values (4,4), 8 and 2 minimizing sets, and middle size (19,48), under each convention. The full classification was not rerun. Root's separate passing replay and registry-refresh receipts are copied and cited, not represented as new runs here.

Every final PDF page was rendered and visually inspected. qa/ and receipts/pdf-qa.json retain the images, hashes and QA findings. Frozen inputs are hash-bound before/after and unchanged. The exact MathDB raw line, sources and access receipts, reviews, search code/data/logs, formal audit, source ZIP, manifests and reproduction instructions are included in middle-dossier.zip. ARCHIVES.sha256 binds both ZIPs. Packaging excludes runtime profiles/caches and duplicate extraction files; the safe-extraction receipt is included. No running jobs remain.

Read REPRODUCE.md for integrity, resource caps, historical replay requirements and limits. Read results.json for machine-readable scope and status.
''')
print('Documentation, eight-page QA receipt, and frozen input check PASS:',len(before),'files')
