from pathlib import Path
import json,hashlib,shutil,zipfile,re,os
R=Path(__file__).resolve().parent;D=R/'dossier'; E=R/'final-replay'
h=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
receipt=json.loads((E/'logs/replay-receipt.json').read_text());assert receipt['status']=='pass'
audit=json.loads((E/'logs/full-audit-summary.json').read_text()); assert audit['status']=='pass'
# Verify all original frozen inputs, byte identity, archive identity, and extracted source manifest.
before=json.loads((R/'receipts/frozen-before.json').read_text());after={name:h(R.parent/name) for name in before}
assert before==after
(R/'receipts/frozen-after.json').write_text(json.dumps(after,indent=2)+'\n')
identity={}
for p in sorted((D/'formal').glob('*.lean')):
 digest=h(p);assert digest==h(R.parent/'xor-magic-formal-r5/formal'/p.name)==h(E/'formal'/p.name);identity[p.name]=digest
manifest=json.loads((D/'source-manifest.json').read_text())
with zipfile.ZipFile(R/'xor-magic-manuscript-source.zip') as z:
 assert z.read('source-manifest.json')==(D/'source-manifest.json').read_bytes()
 assert len(z.namelist())==len(set(z.namelist()))
 assert set(z.namelist())==set(manifest)|{'source-manifest.json'}
 for name,digest in manifest.items():
  assert hashlib.sha256(z.read(name)).hexdigest()==digest==h(E/name)
 assert not any('.olean' in Path(name).suffixes for name in z.namelist())
(R/'receipts/final-source-extraction.json').write_text(json.dumps({'status':'PASS','archive_sha256':h(R/'xor-magic-manuscript-source.zip'),'members':len(manifest)+1,'all_extracted_hashes_match':True,'all_107_lean_modules_byte_identical_r5':True},indent=2)+'\n')
(R/'receipts/lean-identity.json').write_text(json.dumps(identity,indent=2)+'\n')
(R/'receipts/frozen-bindings.json').write_text(json.dumps({'status':'PASS','frozen_files':len(before),'unchanged':True,'aggregate_sha256':hashlib.sha256(json.dumps(before,sort_keys=True).encode()).hexdigest()},indent=2)+'\n')
# Reject banned Lean proof mechanisms, ignoring comments for a precise lexical screen.
bad=[]
for p in (D/'formal').glob('*.lean'):
 s=re.sub(r'/\-.*?\-/','',p.read_text(),flags=re.S);s=re.sub(r'--[^\n]*','',s);s=re.sub(r'"(?:\\.|[^"\\])*"','',s)
 if re.search(r'\b(sorry|admit|axiom|unsafe|native_decide|ofReduceBool)\b',s):bad.append(p.name)
assert not bad,bad
(R/'receipts/source-screen.json').write_text(json.dumps({'status':'PASS','modules':len(identity),'forbidden_tokens':bad,'note':'Comments and string literals excluded; full semantic declaration audit is separate.'},indent=2)+'\n')
resources=receipt['receipts'];assert all(r['wall_seconds']<=140 and r['sampled_aggregate_rss_bytes']<=6*1024**3 for r in resources)
# Only task-specific running processes count. Never terminate or claim absence of sibling work.
running=[]
for p in Path('/proc').iterdir():
 if p.name.isdigit() and int(p.name)!=os.getpid():
  try:
   a=(p/'cmdline').read_bytes().replace(b'\0',b' ').decode(errors='replace');cwd=(p/'cwd').resolve()
   if str(cwd).startswith(str(R)) and any(x in a for x in ['/bin/lean ', '/bin/leanchecker ', 'replay.py', 'tools/bounded.py']):running.append({'pid':p.name,'args':a})
  except OSError:pass
assert not running,running
(R/'receipts/no-running-jobs.json').write_text(json.dumps({'status':'PASS','task_owned_replay_build_checker_jobs':running,'note':'Siblings are outside this lane and untouched.'},indent=2)+'\n')
results={'status':'DRAFT_DOSSIER_REPLAY_PASS_PENDING_ROOT_REVIEW','mathdb_id':372205,'credit':0,'root_accepted':False,'campaign_count':'14/20 beyond 39 unchanged','paper':{'pdf':'xor-magic-draft.pdf','pages':9,'source':'paper-source.md','ai_assisted':True,'priority_claim':False,'qa':'receipts/pdf-qa.json'},'formal':{'modules':107,'byte_identical_to':'xor-magic-formal-r5/formal','strict_replay':'PASS','leanchecker':'PASS','audit':'PASS','unique_declarations':audit['declarations'],'declaration_occurrences':audit['declaration_occurrences'],'negative_controls':len(receipt['negative_controls']),'allowed_axioms':['propext','Classical.choice','Quot.sound'],'endpoints':['XorMagic.corrected_all','XorMagic.not_printed_each_ge_four'],'source_zip_sha256':h(R/'xor-magic-manuscript-source.zip')},'resources':{'max_sampled_aggregate_rss_bytes':max(r['sampled_aggregate_rss_bytes'] for r in resources),'max_wall_seconds':max(r['wall_seconds'] for r in resources),'per_call_cpu_limit_seconds':120,'per_call_wall_limit_seconds':140,'max_cpus':2,'rss_limit_bytes':6*1024**3,'actual_home':str(Path.home())},'frozen_inputs':{'files':len(before),'unchanged':True},'ordinary_bases':{'witnesses':32,'direct_connectivity':'PASS'},'limits':['Batal construction-paper body unread','No new live prior-art search; inherited dated receipts only','Cached upstream oleans trusted','leanchecker shares installation','Sampled RSS is not continuous enforcement','Root final replay and paper review required'],'no_running_jobs':True}
(R/'results.json').write_text(json.dumps(results,indent=2)+'\n')
summary=f'''# XOR-magic manuscript dossier: DRAFT, zero accepted credit

MathDB 372205 / arXiv:2512.19278v1, Conjecture 25. Campaign count remains 14/20 beyond 39. Root alone accepts.

The nine-page AI-assisted draft proves the corrected existence theorem for every n >= 4: all odd open degrees 5 through 2^n-5 and all even closed degrees 4 through 2^n-6. The printed endpoint 2^n-4 is already forbidden by Proposition 24 (Batal); its refutation has zero novelty credit. No priority claim is made.

Both independent-review exposition issues are repaired: every finite base, including order-16 closed degree 6 and order-32 closed degree 4, has a direct descent connectivity certificate; the general lift uses the fully proved component-fibre size argument. Compact seed masks and literal formal definitions appear in the paper. All 32 finite witnesses also pass the separate exact Python check.

Fresh extracted strict replay PASS: 107/107 modules, 107/107 leanchecker invocations, {audit['declarations']} unique declarations ({audit['declaration_occurrences']} audit occurrences), and 17/17 expected-failure negative controls. Lean modules are byte-identical to r5. Only propext, Classical.choice and Quot.sound occur as permitted transitive axioms. All resource receipts satisfy the per-call caps; peak sampled aggregate RSS {results['resources']['max_sampled_aggregate_rss_bytes']} bytes and longest call {results['resources']['max_wall_seconds']:.2f} seconds. Actual HOME retained. A preliminary replay was explicitly stopped and superseded before the authoritative final archive replay.

All nine final PDF pages were rendered and visually inspected. See receipts/pdf-qa.json. All {len(before)} frozen input bindings are unchanged. Source ZIP SHA-256: {h(R/'xor-magic-manuscript-source.zip')}.

Deliverables: xor-magic-draft.pdf; paper-source.md and build_paper.py; corrected PROOF.md; REPRODUCE.md; results.json; xor-magic-manuscript-source.zip; xor-magic-manuscript-full-dossier.zip; source-manifest.json, dossier-manifest.json and archive-hashes.json; receipts/; qa/. Full dossier includes raw MathDB line, source copies, historical review and access receipts, pins and fresh replay logs. Historical evidence retains its original provisional statements; the current proof and final results supersede those statements.

Limits: Batal's construction article body remains unread; no new live prior-art/registry clearance was done. Cached upstream oleans are trusted and leanchecker shares the installation. Sampling is not continuous RSS enforcement. Root must perform its final replay and manuscript review. No task-owned background jobs remain. No git, child agents, ledger edits, publication, browser, accounts or external messages were used.
'''
(R/'SUMMARY.md').write_text(summary)
shutil.copy2(D/'source-manifest.json',R/'source-manifest.json')
# Flat full-dossier root: the source payload plus final deliverables and verified logs.
F=R/'full-dossier';shutil.copytree(D,F,dirs_exist_ok=True)
for name in ['xor-magic-draft.pdf','PROOF.md','paper-source.md','manuscript.md','build_paper.py','certify_bases.py','REPRODUCE.md','SUMMARY.md','results.json','xor-magic-manuscript-source.zip']:
 shutil.copy2(R/name,F/name)
for lane,parts in {'xor-magic-formal-r5':['SUMMARY.md','results.json','REPRODUCE.md','source-manifest.json','statement-correspondence.md','receipts'], 'xor-magic-review-r1':['receipts']}.items():
 for name in parts:
  origin=R.parent/lane/name;target=F/'evidence'/lane/name;target.parent.mkdir(parents=True,exist_ok=True)
  if origin.is_dir():shutil.copytree(origin,target,dirs_exist_ok=True)
  else:shutil.copy2(origin,target)
for name in ['receipts','qa']:
 shutil.copytree(R/name,F/name,dirs_exist_ok=True)
shutil.copytree(E/'logs',F/'replay-logs',dirs_exist_ok=True)
# PDF builder can run without a nested staging directory.
p=F/'build_paper.py';s=p.read_text().replace("R/'dossier/base-data.json'","R/'base-data.json'").replace("R/'dossier/formal/Literal.lean'","R/'formal/Literal.lean'");p.write_text(s)
p=F/'certify_bases.py';s=p.read_text().replace("R/'dossier/formal'","R/'formal'").replace("R/'dossier/base-data.json'","R/'base-data.json'");p.write_text(s)
# Keep the exact source-archive manifest separately from the flat full-root replay manifest.
shutil.copy2(D/'source-manifest.json',F/'source-archive-manifest.json')
full_source_names=json.loads((D/'source-manifest.json').read_text())
(F/'source-manifest.json').write_text(json.dumps({name:h(F/name) for name in full_source_names},indent=2)+'\n')
rp=F/'REPRODUCE.md';rp.write_text(rp.read_text().replace('it omits generated oleans and expression-DAG bulk (their check and audit logs remain)', 'it omits generated oleans and preserves the complete audit expression DAGs'))
with (F/'REPRODUCE.md').open('a') as out:
 out.write('\nFull-root note: source-archive-manifest.json is the exact manifest inside the verified source ZIP. The full-root source-manifest.json instead binds the corresponding full-root replay inputs, including layout adaptations of the PDF builder. For the authoritative Lean replay extract the included source ZIP. The source-only archive PDF builder expects a staging dossier/ containing formal/ and base-data.json; the full dossier PDF builder runs directly at its root.\n')
# Refresh the changed full-root README binding.
fm=json.loads((F/'source-manifest.json').read_text());fm['REPRODUCE.md']=h(F/'REPRODUCE.md');(F/'source-manifest.json').write_text(json.dumps(fm,indent=2)+'\n')
manifest={str(p.relative_to(F)):h(p) for p in sorted(F.rglob('*')) if p.is_file() and p.name!='dossier-manifest.json'}
(F/'dossier-manifest.json').write_text(json.dumps(manifest,indent=2)+'\n');shutil.copy2(F/'dossier-manifest.json',R/'dossier-manifest.json')
with zipfile.ZipFile(R/'xor-magic-manuscript-full-dossier.zip','w',zipfile.ZIP_DEFLATED) as z:
 for p in sorted(F.rglob('*')):
  if p.is_file():z.write(p,p.relative_to(F))
archives={name:h(R/name) for name in ['xor-magic-manuscript-source.zip','xor-magic-manuscript-full-dossier.zip']}
(R/'archive-hashes.json').write_text(json.dumps(archives,indent=2)+'\n')
# Read archive bytes independently and verify every payload member without extra extraction.
with zipfile.ZipFile(R/'xor-magic-manuscript-full-dossier.zip') as z:
 assert z.testzip() is None
 assert set(z.namelist())==set(manifest)|{'dossier-manifest.json'}
 for name,digest in manifest.items():assert hashlib.sha256(z.read(name)).hexdigest()==digest
(R/'receipts/full-dossier-verification.json').write_text(json.dumps({'status':'PASS','members':len(manifest)+1,'full_zip_sha256':archives['xor-magic-manuscript-full-dossier.zip'],'all_payload_hashes_match':True},indent=2)+'\n')
print(json.dumps(results,indent=2))
