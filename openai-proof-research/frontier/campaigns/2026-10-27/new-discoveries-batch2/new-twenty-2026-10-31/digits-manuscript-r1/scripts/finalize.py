from pathlib import Path
import hashlib,json,zipfile,os,datetime
W=Path(__file__).resolve().parents[1];os.chdir(W)
def sha(p):return hashlib.sha256(Path(p).read_bytes()).hexdigest()
report=json.loads(Path('fresh-replay/receipts/replay.json').read_text());assert report['status']=='PASS'
before=json.loads(Path('input-hashes-before.json').read_text());after={p:sha(p) for p in before};assert before==after
Path('input-hashes-after.json').write_text(json.dumps(after,indent=2)+'\n')
assert sha('formal/Digits.lean')=='0bb3177a827bb4499b2671253b34ef04bd24899975ada71ae86890986d8727fa'
assert sha('formal/Audit.lean')==sha(W.parent/'expanded-corpus-r107/lean/Audit.lean')
assert sha('evidence/356756-proof-source.zip')=='a75bec77dd1840d641693364891b85f96a8d0e8758c9c117f3a17c3e2c4e89ee'
assert sha('digits-source-only.zip')==json.loads(Path('receipts/extraction.json').read_text())['sha256']
for f,digest in json.loads(Path('SOURCE-MANIFEST.json').read_text()).items():assert sha(f)==digest and sha(Path('fresh-replay')/f)==digest,f
rs=[json.loads(p.read_text()) for p in Path('fresh-replay/receipts').glob('*.json') if p.name!='replay.json']
assert all(r['killed'] is None and r['seconds']<140 and r['peak_RSS_KiB']<=6*1024*1024 for r in rs)
qa=json.loads(Path('receipts/pdf-visual-qa.json').read_text());assert qa['pdf_sha256']==sha('paper/digits-parity-draft.pdf')
results=dict(mathdb_id=356756,status='DRAFT_READY_FOR_ROOT_REVIEW',accepted_credit=0,title='A parity certificate for a conjectured four-term progression-free digit family',paper=dict(pdf='paper/digits-parity-draft.pdf',source='paper/build_paper.py',pages=6,visual_qa='PASS'),formal=dict(report,receipt='fresh-replay/receipts/replay.json',full_audit_log='fresh-replay/logs/build-AuditFull.log',max_sampled_RSS_KiB=max(r['peak_RSS_KiB'] for r in rs),max_wall_seconds=max(r['seconds'] for r in rs),source_modules_byte_identical=True),frozen_inputs=dict(files=len(before),unchanged=True,receipt='receipts/frozen-bindings.json'),archives=['digits-source-only.zip','digits-full-dossier.zip'],novelty='Exact uniform admissibility; no record bound or priority claim. Bounded prior-art comparison inherited from review/root; no new live refresh in drafting pass.',limits=['Cached upstream mathlib oleans trusted; not rebuilt or source-attested','Stirling bound and literature comparisons not formalized','General equal-histogram extension established in ordinary proof; frozen Lean endpoint uses SourceSet','Root alone performs final independent replay, paper review, registry refresh and acceptance'],bibliographic_correction='The file sieb-thesis.pdf is Jakob Führer’s September 2024 thesis, identified from title page.',integrity=dict(no_git=True,no_children=True,no_shared_edits=True,no_external_messages=True,no_browser=True,no_publication=True,write_scope=str(W),jobs_at_handback=0),prior_attempts='preliminary-replay records the hidden-decidability negative-control issue; pre-final-replay passed before the final bibliography correction. Final fresh-replay is operative.',manifest_scope='DOSSIER-MANIFEST.json binds the full ZIP payload. Self-referential archive/manifest hashes and the post-archive integrity receipt are external.',utc=datetime.datetime.now(datetime.timezone.utc).isoformat())
Path('results.json').write_text(json.dumps(results,indent=2)+'\n')
Path('SUMMARY.md').write_text(f'''# MathDB 356756: draft manuscript and reproducible dossier

**Ready for root review; zero accepted credit.** The six-page AI-assisted draft proves exact admissibility of the conjectured digit family using the parity-corrected potential. It states the full source objects, classifies every wrap orientation, proves both gap formulas and the summation, and explains the uniform dual certificate. It makes no record or priority claim and records the EHPS comparison and source computations honestly.

Deliverables:

- `paper/digits-parity-draft.pdf` and editable `paper/build_paper.py`.
- `PROOF.md` and `STATEMENT-CORRESPONDENCE.md`.
- Byte-identical `formal/Digits.lean` and `formal/Audit.lean`; new full-body `formal/AuditFull.lean`.
- `digits-source-only.zip`, portable `replay.py`, `REPRODUCE.md` and negative controls.
- `digits-full-dossier.zip`, source copies, HTTP/search receipts and exact hashed raw MathDB line.
- Input/copy/module/source/dossier manifests, archive hashes, `results.json`, QA images and receipts.

Final safe extracted replay: **PASS**. Three strict builds and three per-module leanchecker runs passed. AuditFull printed and checked all **45 declarations, 45 full types and 45 bodies**, including generated declarations; only propext, Classical.choice and Quot.sound occur. Both false Lean variants failed for the intended mathematical reason. Existing-olean refusal was exercised. Peak sampled RSS was {results['formal']['max_sampled_RSS_KiB']:,} KiB; the longest subprocess was {results['formal']['max_wall_seconds']:.2f} s. Every final subprocess respected the two-CPU, sampled 6 GiB, 120 CPU-second and 140 wall-second caps. Receipts: `fresh-replay/receipts/replay.json` and adjacent per-call receipts; full audit: `fresh-replay/logs/build-AuditFull.log`.

All six PDF pages were rendered and visually inspected; `receipts/pdf-visual-qa.json` binds the final PDF and images. The misleading cached `sieb-thesis.pdf` filename was resolved from the title page: it is Jakob Führer’s 2024 thesis. The frozen file was not changed.

All **{len(before)} frozen input files** match their before/after SHA-256 bindings. The required Digits and source-packet hashes match exactly. No git, child agents, browser, publication, external messages, shared ledger edits or writes outside this lane were used. No started jobs remain at handback. The first negative control failed initially for a hidden decidability instance; after unfolding its definitions it rejects the false proposition itself. Earlier attempts are retained transparently; final fresh-replay is operative.

Trust limits: cached upstream oleans are trusted, not source-attested. The general histogram strengthening, Stirling consequence and literature comparison are ordinary mathematics beyond the exact frozen SourceSet endpoint. Prior-art clearance is the inherited bounded review/root record, not exhaustive coverage or a new live refresh. Root alone accepts, refreshes registries and performs its final independent replay and paper review.

`DOSSIER-MANIFEST.json` binds the files inside the full ZIP (excluding itself); the full ZIP also carries that manifest. `archive-hashes.json` and `receipts/archive-integrity.json` are external post-archive bindings to avoid self-reference. Temporary Python dependencies are not part of the delivered dossier archive.
''')
# Final inventory excludes local installation caches and obsolete build products.
exclude_roots={'tmp'};exclude_names={'digits-full-dossier.zip','archive-hashes.json','DOSSIER-MANIFEST.json','receipts/archive-integrity.json'}
files=[]
for p in sorted(Path('.').rglob('*')):
 if not p.is_file() or p.parts[0] in exclude_roots or str(p) in exclude_names:continue
 if '__pycache__' in p.parts:continue
 if p.parts[0] in {'preliminary-replay','pre-final-replay'} and '.olean' in p.name:continue
 files.append(p)
manifest={str(p):sha(p) for p in files}
Path('DOSSIER-MANIFEST.json').write_text(json.dumps(manifest,indent=2)+'\n')
with zipfile.ZipFile('digits-full-dossier.zip','w',zipfile.ZIP_DEFLATED) as z:
 for p in files+[Path('DOSSIER-MANIFEST.json')]:z.write(p,str(p))
with zipfile.ZipFile('digits-full-dossier.zip') as z:
 assert z.testzip() is None
 for f,digest in manifest.items():assert hashlib.sha256(z.read(f)).hexdigest()==digest
 ah={p:dict(sha256=sha(p),bytes=Path(p).stat().st_size) for p in ['digits-source-only.zip','digits-full-dossier.zip']}
Path('archive-hashes.json').write_text(json.dumps(ah,indent=2)+'\n')
Path('receipts/archive-integrity.json').write_text(json.dumps(dict(status='PASS',payload_files=len(manifest),crc_check='PASS',all_member_hashes='PASS',archives=ah),indent=2)+'\n')
print(json.dumps(dict(status='PASS',replay=report,archives=ah,frozen_files=len(before)),indent=2))
