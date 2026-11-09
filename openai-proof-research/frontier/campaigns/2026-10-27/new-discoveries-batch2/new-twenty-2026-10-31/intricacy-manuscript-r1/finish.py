from pathlib import Path
import json,shutil,hashlib,zipfile,re,datetime
r=Path(__file__).resolve().parent;d=r/'dossier'
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
p=d/'validate_complete.py';s=p.read_text();s=s.replace("out=Path(sys.argv[1])", "if (r/'SHA256SUMS.json').exists():\n for f,h in json.loads((r/'SHA256SUMS.json').read_text()).items():\n  assert hashlib.sha256((r/f).read_bytes()).hexdigest()==h, f\nout=Path(sys.argv[1])")
s=s.replace("cache=Path(","assert hashlib.sha256(lean.read_bytes()).hexdigest()==json.loads((r/'candidate/pins.json').read_text())['lean_binary_sha256']\ncache=Path(")
s=s.replace("assert len(inv)==444", "assert {x['module'] for x in inv}==set(mods)\nassert len(inv)==444")
s=s.replace("named=json.loads", "expected=json.loads((r/'fidelity-review/complete-inventory.json').read_text())\n# Compare actual inventory names below in addition to the independent count.\nnamed=json.loads")
# exact names from reviewed log, regardless of JSON layout
s=s.replace("assert set(named)<=", "oldlog=(r/'fidelity-review/complete-inventory.log').read_text()\nassert {x['name'] for x in inv}==set(re.findall(r'INVENTORY\\|[^|\\n]+\\|([^|\\n]+)\\|',oldlog))\nassert set(named)<=")
p.write_text(s)
shutil.copyfile(r/'work/tex/paper.pdf',r/'paper.pdf')
for f in ['paper.pdf','paper.tex','input-bindings.json','integrity-before.json']:shutil.copyfile(r/f,d/f)
for f in ['audit-inventory.json','EndpointStatement.lean']:
 shutil.copyfile(r.parent/'intricacy-entropy-r5'/f,d/'candidate'/f)
reg=json.loads((d/'fresh-context/registry-reuse.json').read_text());assert sha(Path(reg['path']))==reg['prior_receipt']['sha256'];shutil.copyfile(reg['path'],d/'fresh-context/registry-head.json')
(d/'logs').mkdir(exist_ok=True)
for p in (r/'work/replay').iterdir():
 if p.is_file():shutil.copyfile(p,d/'logs'/p.name)
shutil.copyfile(r/'work/tex/paper.log',d/'logs/paper-build.log')
(d/'REPRODUCE.md').write_text('''# Reproduction and trust limits

This is a draft dossier, not root acceptance. Candidate credit 0; campaign 1/20 unchanged.

1. Extract this outer ZIP to a new directory. Verify every file against SHA256SUMS.json using Python hashlib.sha256. The hash file excludes itself to avoid self-reference.
2. Run `python3 validate_complete.py /absolute/path/to/a/new/replay-output`. The output directory may exist but its `extracted` child must not. Use a path within the authorized review lane. Python 3 standard library suffices. The script does not run the original author validator, whose 238-name regex omits generated helpers.
3. It verifies bundled hashes and the Lean executable pin; rejects unsafe archive paths, symlinks, files over 40 MB and compiled proof objects; extracts the unchanged original packet; verifies every mathematical source against the separately bundled frozen bytes; builds all 21 mathematical modules, the unchanged author audit, then the unchanged independent inventory. Every compiler invocation is sequential, `-j2 -M4096 -DwarningAsError=true`, affinity at most 2 CPUs, 180 CPU seconds and 240 wall seconds per module. The environment contains only PATH, HOME inside output, LANG and explicit LEAN_PATH.
4. The validator enumerates originating-module constants using Lean's environment and `Lean.collectAxioms`, includes generated definitions, checks exact equality with the independently reviewed 444-name set, verifies coverage of all 238 named declarations, and rejects local axioms, unsafe declarations and transitive axioms beyond propext, Classical.choice, Quot.sound. See IndependentInventory.lean and logs/complete-inventory.json. The endpoint is printed with its actual type and transitive axioms in IndependentInventory.log.
5. The tool paths and dependency cache are explicit in validate_complete.py and candidate/pins.json. Lean 4.34.1 binary hash is checked. Mathlib is pinned to d13f23b723b8a846827a245b89c10fc7d3f11612; all package revisions are in candidate/lake-manifest.json. On another machine provision the pinned Lean and packages and adjust only those paths, documenting the change. No package download or upstream rebuild is performed by this validator.
6. Upstream prebuilt oleans and exported axiom summaries are trusted. Metadata does not prove source-to-olean correspondence; this is not a full upstream rebuild or independent-kernel attestation. The original replay.sh has historical absolute paths and CPU IDs: use the augmented validator for this dossier.
7. Rebuild the paper with a TeX distribution supporting amsmath, amsthm, mathtools, geometry, lmodern, microtype and hyperref, e.g. `tectonic --keep-logs paper.tex`. PDF byte identity is not promised across TeX builds because metadata can change. The supplied nine-page PDF was rendered and every page visually inspected; the final build has zero TeX warnings. Render intermediates, local oleans and caches are intentionally excluded.

The sole nested archive is the explicitly requested unchanged original proof packet. Historical reviews and source versions are retained as evidence, not assertions of today's priority. Source receipts are inherited dated HTTP evidence, not new requests by this worker. See SOURCE-COMPARISON-LIMITS.md and both review reports. Independent paper review, root final replay and acceptance remain separate.
''')
(d/'SOURCE-COMPARISON-LIMITS.md').write_text('''# Bounded source comparison

The paper's Section 9 states the primary-body comparison. This worker reread the cached source conjectures, relevant Markov/entropy formulas, predecessor sparse-support construction/proof and Huang-Xiao Section 5 proof bodies. No new external retrieval was made; inherited receipts retain exact URLs, retrieval dates and hashes in source-review/receipts.jsonl and fresh-context/receipts.jsonl. Source bytes are separately hashed by SHA256SUMS.json. The recent registry head body is bundled and rehashed, but is a head receipt only.

Petersen 1607.02425v1 Conjecture 4.6.8 and Petersen-Wilson 1512.01143v6 Conjecture 6.3 ask the exact fully supported local one-step maximum. PW Proposition 5.10 proves the conditional-entropy/geometric-gap series; Proposition 5.5 optimizes Asc over invariant laws. Its Section 6 numerical evidence and independent-line zero formula do not establish the transverse sign here. Buzzi-Zambotti 0909.2120v2 builds length-dependent finite laws using occupancy estimates; no consistent one-step Markov family follows from that inspected construction. Huang-Xiao 2509.20738v1 Theorems 5.1-5.2 optimize system-level/fixed-cover Asc using variational principles and ergodic decomposition; those proof mechanisms do not give this transverse Int maximum. No complete subsumer found in the specified inspected bodies; not a worldwide novelty claim.

Uninspected limits remain Wilson's 2015 dissertation body (not located), Buzzi-Zambotti's 2012 symmetry-breaking body, Li-Tu and other citing/pressure/random-bundle full bodies, all earlier arXiv versions, PW's publisher body (public 403; no retry/bypass), Huang-Xiao's complete publisher body (landing page only), all citing literature and current registry proof bodies. MathDB and Palomar denied access was not retried. The cached normalized record is not live authentication. No missing body is declared a fatal bridge merely because it is unread; a concrete equivalent transverse theorem or substitutable binary-channel inequality would materially change the bounded qualified judgment.

Ordinary/source/significance review: inherited QUALIFIED_PASS. Formal/fidelity review: four gates PASS within its stated remit. The historical source review's NOT_PROVED_NOT_REVIEWED formal status predates r5 and is superseded only on formal fidelity by that separate frozen review, not on priority. Lean completion is not novelty evidence. Candidate credit stays 0 pending root; accepted campaign stays 1/20.
''')
shutil.copyfile(d/'SOURCE-COMPARISON-LIMITS.md',r/'SOURCE-COMPARISON-LIMITS.md')
# All 59 originals are checked again after writing the paper and reproduction material.
x=json.loads((r/'input-bindings.json').read_text());rows=[dict(path=p,expected=h,actual=sha(Path(p))) for p,h in x.items()];assert all(t['expected']==t['actual'] for t in rows)
(r/'integrity-after.json').write_text(json.dumps(rows,indent=2)+'\n');shutil.copyfile(r/'integrity-after.json',d/'integrity-after.json')
qa=dict(pages=9,rendered_all=True,visually_inspected_pages=list(range(1,10)),final_changed_pages_reinspected=[2,8,9],other_final_render_pages_byte_identical=True,overflow=False,tex_warnings=0,render_intermediates_bundled=False)
(r/'pdf-qa.json').write_text(json.dumps(qa,indent=2)+'\n');shutil.copyfile(r/'pdf-qa.json',d/'pdf-qa.json')
manifest={str(p.relative_to(d)):sha(p) for p in sorted(d.rglob('*')) if p.is_file() and p.name!='SHA256SUMS.json'}
(d/'SHA256SUMS.json').write_text(json.dumps(manifest,indent=2)+'\n')
with zipfile.ZipFile(r/'dossier.zip','w',zipfile.ZIP_DEFLATED) as z:
 for p in sorted(d.rglob('*')):
  if p.is_file():
   assert p.suffix not in ['.olean','.ilean','.png','.so'];z.write(p,p.relative_to(d))
print('ZIP',sha(r/'dossier.zip'),'files',len(manifest)+1)
