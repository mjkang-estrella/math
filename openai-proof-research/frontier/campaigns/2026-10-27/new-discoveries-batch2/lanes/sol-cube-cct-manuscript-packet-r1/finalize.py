from pathlib import Path
import hashlib,json,subprocess,sys,zipfile
L=Path(__file__).resolve().parent;sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
records=json.loads((L/'freeze.json').read_text())
for r in records:assert sha(Path(r['original']))==sha(L/r['copy'])==r['sha256']
(L/'before-after.json').write_text(json.dumps({'status':'PASS','scientific_inputs':len(records),'originals_and_copies_unchanged':True,'records':records,'administrative':'snapshot only; no live bindings'},indent=2)+'\n')
new=json.loads((L/'fresh-extraction/actual-audit.json').read_text());old=json.loads((L/'packet/actual-audit.json').read_text())
assert new==old and new['count']==134
subprocess.run([sys.executable,str(L/'fresh-extraction/rebuild_zip.py'),str(L/'rebuilt-after-replay.zip')],check=True)
assert (L/'source-only.zip').read_bytes()==(L/'rebuilt-after-replay.zip').read_bytes()
for sub in ['packet/formal','fresh-extraction/formal']:
 F=L/sub
 for n,h in json.loads((F/'source-manifest.json').read_text()).items():assert sha(F/n)==h
 for p in F.glob('*.olean'):p.unlink()
 for p in F.glob('*.ilean'):p.unlink()
builds=[json.loads((L/'fresh-extraction/formal'/f'{m}.guard.json').read_text()) for m in ['Finite','Cube','Endpoint','Audit']]
receipt={'status':'PASS','count':134,'module_counts':{'Finite':92,'Cube':10,'Endpoint':32},'safe':True,'partials':[],'allowed_axioms':['propext','Classical.choice','Quot.sound'],'full_types_identical_between_replays':True,'fresh_archive_extraction':True,'zip_rebuild_identical_after_replay':True,'builds':builds,'immutable_formal_archive_sha256':'ead8a07b9a339d55285f12e37f96fb6834a58007988160e8df8a8a864e3c595d','source_zip_sha256':sha(L/'source-only.zip'),'PDF':'BLOCKED','novelty':'HOLD'}
(L/'fresh-extracted-replay.json').write_text(json.dumps(receipt,indent=2)+'\n')
result='''# Manuscript packet result

Complete manuscript source prepared, designed for four pages. Main theorem:
the full real linear five-cube group is not CCT on the Boolean algebra of
its 32 vertices; published Question 6.6 is therefore negative. The paper
contains the classical cover definition, both deletions, explicit A and
inverse, full-group pair-sum proof, all 36 weights, unique score 51 at 13,
and the 2-versus-16 contradiction. No main Peckness, minimum witness,
lower-dimensional classification or universal formal claim is made.

The published source DOI is 10.1007/s11083-016-9408-x, online 2016-10-06,
journal Order34(2017)441-463. Actual classical/reconstruction bodies were
inspected in their frozen copies; the paper states exact local coverage
and does not present earlier reviews' broader coverage as fresh reading.

PDF BLOCKED. The mandatory marker failed twice under the unchanged 512MiB
guard, with the permitted low-memory flags. No PDF was authored, rendered
or visually checked. Four pages is a source design, not a verified PDF
page count. PDF byte reproducibility is unverified. The unexecuted renderer
is supplied as source with explicit instructions for the marker and QA.

Formal PASS. The original archive SHA is
ead8a07b9a339d55285f12e37f96fb6834a58007988160e8df8a8a864e3c595d.
All mathematical sources and Audit.lean are byte unchanged. Both this lane's
original-runner replay and a fresh ZIP extraction using the portable runner
passed strict serial Lean checks and full 134 actual-declaration audits.
Their full types match exactly; no partials; all safe; only Std3 axioms.
Compiler, manifest and all nine package heads were checked without git.
Inherited library oleans are used; mathlib was not rebuilt or exhaustively
authenticated. Replay receipts retain the fixed resource measurements.

ZIP SHA256: ZIPHASH
57 source/evidence members, no own compiled artifacts. Fresh extracted
rebuilds before and after replay are byte identical. See archive-rebuild.json,
fresh-extracted-replay.json and packet/README.md for reproduction details.

Novelty and acceptance remain HOLD. Current public-registry heads/bodies,
comprehensive citing coverage, the parked Wiley403 original, Godsil-Kocay1982
and closest binary-code pseudosimilarity gaps remain explicit. Packet
preparation clears none of them. No new retrieval, shared/git/public/browser/
MathDB action or child agent. Root alone accepts/counts: 9/39/next40 unchanged.

Final manifest excludes itself and verification-receipt.json. A separate
guarded verification invocation must run after this result and manifest
are written. All scientific originals and frozen copies match before/after.
'''.replace('ZIPHASH',sha(L/'source-only.zip'))
(L/'RESULT.md').write_text(result)
manifest={str(p.relative_to(L)):sha(p) for p in sorted(L.rglob('*')) if p.is_file() and p.name not in ['manifest.json','verification-receipt.json']}
(L/'manifest.json').write_text(json.dumps(manifest,indent=2,sort_keys=True)+'\n')
print('Finalized',len(manifest),'files; separate verification still required')
