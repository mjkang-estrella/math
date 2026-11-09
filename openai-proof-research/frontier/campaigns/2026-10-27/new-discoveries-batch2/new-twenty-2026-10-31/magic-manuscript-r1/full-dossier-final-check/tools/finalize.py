from pathlib import Path
import json,hashlib,shutil,zipfile,datetime
R=Path(__file__).resolve().parents[1]
def sha(p): return hashlib.sha256(p.read_bytes()).hexdigest()
def dump(n,o): (R/n).write_text(json.dumps(o,indent=2))
replay=json.loads((R/'replay-extraction-r4/replay-receipts/result.json').read_text());assert replay['status']=='PASS'
shutil.copytree(R/'replay-extraction-r4/replay-receipts',R/'receipts/final-replay',dirs_exist_ok=True)
for attempt in ['fresh-extraction','fresh-extraction-final','replay-extraction-r3']:
 out=R/'receipts/earlier-attempts'/attempt;out.mkdir(parents=True,exist_ok=True)
 shutil.copytree(R/attempt/'replay-receipts',out/'replay-receipts',dirs_exist_ok=True)
 shutil.copyfile(R/attempt/'replay.py',out/'replay.py')
dump('receipts/earlier-attempts/NOTES.json',{
 'fresh-extraction':'Build, leanchecker and Lean audit passed. Python audit parser lacked DOTALL and rejected line-wrapped lists.',
 'fresh-extraction-final':'Build, checker and audit passed. Positive sanity needed explicit unfolding of IsSuperEdgeMagic before decide.',
 'replay-extraction-r3':'Build, checker, audit, sanity, wrong-constant and wrong-endpoint rejection passed; case-sensitive diagnostic matcher expected lowercase type mismatch but Lean printed Type mismatch.',
 'resolution':'Only reviewer harness changed; literal Magic.lean untouched. Final source archive replay in replay-extraction-r4 PASS with case-insensitive diagnostics and explicit unfold.'})
source=json.loads((R/'source-manifest.json').read_text())
with zipfile.ZipFile(R/'source-only-proof.zip') as z:
 assert set(z.namelist())==set(source)|{'source-manifest.json'}
 for n,d in source.items():
  assert hashlib.sha256(z.read(n)).hexdigest()==d==sha(R/n)
  assert sha(R/'replay-extraction-r4'/n)==d
 assert not any(n.endswith('.olean') for n in z.namelist())
dump('receipts/source-archive-verification.json',{'status':'PASS','members':len(source)+1,'zip_sha256':sha(R/'source-only-proof.zip'),'fresh_safe_extraction':'replay-extraction-r4','all_manifest_hashes_match':True,'no_oleans_in_archive':True})
results={'status':'DRAFT_COMPLETE','mathdb_id':381805,'ordinary_exact_strength':26,'conjectured_strength':27,
 'formal_endpoint':'Magic381805.source_refutation : ¬Magic381805.SourceConjecture',
 'formal_strength_upper_bound':26,'formal_exact_lower_bound':False,'lean_replay':replay,
 'paper_pages':5,'visual_QA':'PASS: all final rendered pages inspected','frozen_inputs_unchanged':True,'frozen_file_count':685,
 'prior_art':'Bounded review; original-body gaps disclosed; no priority claim. Review HOLD preserved alongside root QUALIFIED_PASS.',
 'accepted_credit':0,'campaign_count':'9/20 beyond 39 unchanged','root_alone_accepts':True,
 'literal_module_sha256':sha(R/'proof/Magic.lean'),'raw_mathdb_sha256':sha(R/'raw/381805.jsonl'),
 'publication_upload_external_messages':False,'child_agents':0,'no_git_operations':True,
 'deliverables':['paper.pdf','paper-source.json','build_paper.py','PROOF.md','REPRODUCE.md','source-only-proof.zip','full-dossier.zip'],
 'scope_limits':['No all-positive-leaf counterexample established','Exact minimum lower bound ordinary only','Cached dependency oleans trusted','No exhaustive novelty clearance'],
 'utc':datetime.datetime.now(datetime.timezone.utc).isoformat()}
dump('results.json',results)
summary='''# MathDB 381805 - DRAFT dossier

The five-page manuscript proves in ordinary mathematics that the seven-cycle
with four leaves at one vertex has super edge-magic total strength exactly 26.
The complete vertex/edge certificate gives 26; degree rearrangement gives
11c >= 98 + 187 = 285 and hence c >= 26. Deepthi's predicted value is 27.
The source domain and the role of zero pendant counts are stated explicitly.

The literal proof/Magic.lean is byte-identical to the frozen author module.
Its endpoint is Magic381805.source_refutation : ¬SourceConjecture, via the
upper bound strength <= 26. The exact lower bound is NOT claimed formalized.
The Lean correspondence table separates these results and the diagnostics.

Fresh safe extraction of source-only-proof.zip into replay-extraction-r4 passed:
strict -j1 -DwarningAsError=true build; leanchecker; all 37 module-origin
declarations audited, with bodies and no unsafe/partial flags; transitive axioms
restricted to propext, Classical.choice and Quot.sound; one positive sanity
control and six negative controls with their precise expected failures.
Receipts and logs: receipts/final-replay/. Earlier harness failures are preserved
and explained under receipts/earlier-attempts/; the mathematical module never changed.
Each final call had 2-CPU affinity, CPU 120 s and wall 140 s caps, AS 64 GiB,
sampled private RSS guard 6 GiB, MALLOC_ARENA_MAX=2 and a functioning systemd
MemoryMax=6G scope. Imported cached dependency oleans remain trusted.

All five final PDF pages were rendered and visually inspected (qa/QA.json).
The absent optional PDF-skill artifact hook is recorded in receipts/artifact-marker.json.
All 685 frozen input bindings match before and after; formal/Magic.lean identity
and the raw MathDB record hash are recorded in receipts/frozen-check.json.
Target-related source copies and access receipts are retained; unrelated
382220/382141 mathematical payloads are excluded. The binding inventories
cover entire frozen inputs without copying their unrelated contents.

Related work states the reproduced Swaminathan-Jeyanthi bounds 26 <= sm <= 27;
the unread 2003/2006, 2000/2001 and 2001 original bodies are named. Original
review HOLDs and root's later bounded qualified ruling are both preserved.
There is no priority claim and no inferred all-positive-leaf theorem.
The 831,600-assignment enumeration and mixed infeasible/timeout MILPs are
inherited diagnostics, explicitly separate from proof and not rerun here.

Deliverables: paper.pdf, paper-source.json, build_paper.py, PROOF.md,
REPRODUCE.md, pins.json, replay.py, safe_extract.py, source-manifest.json,
dossier-manifest.json, source-only-proof.zip, full-dossier.zip,
archive-hashes.json, results.json, sources/, evidence/, receipts/ and qa/.
The source ZIP has no oleans; the full ZIP adds final receipts and excludes
local vendor dependencies and generated oleans. See REPRODUCE.md for replay
instructions, trust assumptions, resource guards and manifest exclusions.

DRAFT; zero accepted credit; campaign remains 9/20 beyond 39 unchanged.
Root alone accepts. No child agents, git, publication, upload, external messages,
browser use or shared ledger edits. All launched jobs completed before handback.
'''
(R/'SUMMARY.md').write_text(summary)
# Full archive is a minimal dossier, not recursive copies of extraction trees or vendors.
names=set(source)|{'source-manifest.json','SUMMARY.md','results.json','frozen-before.json','frozen-after.json','frozen-final-check.json','TASK.txt','tools/finalize.py'}
for directory in ['receipts','qa']:
 names.update(str(p.relative_to(R)) for p in (R/directory).rglob('*') if p.is_file())
names.difference_update({'receipts/finalize.log','receipts/finalize.receipt.json'})
assert not any(n.endswith('.olean') for n in names)
manifest={n:sha(R/n) for n in sorted(names)}
dump('dossier-manifest.json',manifest)
with zipfile.ZipFile(R/'full-dossier.zip','w',zipfile.ZIP_DEFLATED) as z:
 for n in sorted(names): z.write(R/n,n)
 z.write(R/'dossier-manifest.json','dossier-manifest.json')
dump('archive-hashes.json',{n:{'sha256':sha(R/n),'bytes':(R/n).stat().st_size} for n in ['source-only-proof.zip','full-dossier.zip']})
print('Finalized',len(names)+1,'full members',replay['status'])
