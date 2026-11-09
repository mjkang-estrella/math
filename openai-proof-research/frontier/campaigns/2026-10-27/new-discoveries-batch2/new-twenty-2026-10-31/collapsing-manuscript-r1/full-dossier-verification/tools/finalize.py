from pathlib import Path
import hashlib,json,zipfile,shutil,subprocess,os,time
D=Path(__file__).resolve().parents[1];B=D.parent
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
shutil.copytree(D/'fresh-extraction/replay-receipts',D/'replay-receipts',dirs_exist_ok=True)
before=json.loads((D/'frozen-before.json').read_text())
roots=[B/'expanded-corpus-r73',B/'collapsing-review-r2',B/'collapsing-prior-r3',B/'collapsing-root-adjudication-r1.json']
after={str(p.relative_to(B)):sha(p) for root in roots for p in ([root] if root.is_file() else sorted(root.rglob('*'))) if p.is_file()}
assert before==after,'frozen input changed'
(D/'frozen-after.json').write_text(json.dumps(after,indent=2))
source=json.loads((D/'source-manifest.json').read_text())
assert all(sha(D/n)==h and sha(D/'fresh-extraction'/n)==h for n,h in source.items())
with zipfile.ZipFile(D/'source-only-proof.zip') as z:
 assert set(z.namelist())==set(source)|{'source-manifest.json'}
 assert all(hashlib.sha256(z.read(n)).hexdigest()==h for n,h in source.items())
 assert not any(n.endswith(('.olean','.ilean')) for n in z.namelist())
for p in (D/'proof').glob('*.lean'):
 assert sha(p)==sha(B/'expanded-corpus-r73/lean-packet/proof'/p.name)
r=json.loads((D/'replay-receipts/result.json').read_text());assert r['status']=='PASS'
(D/'receipts/source-archive-verification.json').write_text(json.dumps({'status':'PASS','source_zip_sha256':sha(D/'source-only-proof.zip'),'all_manifest_members_verified':len(source),'fresh_extraction_sources_equal':True,'literal_lean_sources_byte_identical':True,'precompiled_in_source_archive':False},indent=2))
(D/'receipts/frozen-check.json').write_text(json.dumps({'status':'PASS','files':len(before),'before_sha256':sha(D/'frozen-before.json'),'after_sha256':sha(D/'frozen-after.json'),'same_names_and_bytes':True},indent=2))
# Check processes attributable to this lane, excluding this finalizer and its resource wrapper/ancestors.
anc=set();pid=os.getpid()
while pid>1:
 anc.add(pid)
 try:pid=int((Path('/proc')/str(pid)/'stat').read_text().rsplit(')',1)[1].split()[1])
 except (OSError,ValueError):break
jobs=[]
for p in Path('/proc').glob('[0-9]*'):
 try:
  if int(p.name) in anc:continue
  cmd=(p/'cmdline').read_bytes().replace(b'\0',b' ').decode(errors='replace')
  if str(D) in cmd:jobs.append({'pid':int(p.name),'command':cmd})
 except OSError:pass
assert not jobs,jobs
(D/'receipts/no-running-jobs.json').write_text(json.dumps({'status':'PASS','utc':time.strftime('%Y-%m-%dT%H:%M:%SZ',time.gmtime()),'active_lane_child_jobs':jobs,'note':'Finalizer and its synchronous wrapper/ancestors excluded; all build, checker, audit, controls and rendering children completed.'},indent=2))
results={'status':'DRAFT','mathdb_id':378395,'accepted_credit':0,'campaign_count':'11/20 beyond 39 unchanged','acceptance_authority':'root alone','priority_claim':False,'manuscript_pages':8,'replay':'PASS','strict_flags':['-j1','-DwarningAsError=true'],'leanchecker':'PASS','audited_declarations':134,'allowed_axioms':r['allowed_axioms'],'negative_controls_rejected':5,'positive_harness_controls':1,'literal_lean_byte_identical':True,'input_bindings_unchanged':True,'protected_files':len(before),'pdf_QA':'PASS: eight pages individually inspected','systemd_MemoryMax_6G':r['systemd_scope_MemoryMax_6G'],'max_private_RSS_bytes':r['max_sampled_private_rss_bytes'],'max_total_VmRSS_bytes':r['max_sampled_total_vmrss_bytes'],'max_subprocess_wall_seconds':r['max_wall_seconds'],'endpoint':'MathDB378395.Main.collapsing_conjecture_false','limitations':['No priority claim; bounded prior-art evidence only.','Schroeter enumeration disclosed; no explicit older representative matched.','Independent novelty HOLD and root qualified pass both retained.','Dobra later-open report from frozen adjudication; no independently read primary body supplied.','Pinned dependency oleans trusted; no upstream rebuild.'],'running_jobs':0}
(D/'results.json').write_text(json.dumps(results,indent=2))
(D/'SUMMARY.md').write_text('''# DRAFT - MathDB 378395

Eight-page manuscript: paper.pdf; editable source: paper-source.json and build_paper.py. PROOF.md contains the complete ordinary proof. Explicit integer matrices define a valid functional on P^{4,4,5}; a determinant-one minor certifies 43 independent tight columns; consistency relations give cone dimension 44; five distinct zero patterns obstruct all state-map pullbacks to four layers.

Fresh safe-extraction replay of source-only-proof.zip: PASS. Strict -j1 -DwarningAsError=true build, leanchecker, full audit of 134 declarations (38 definitions, 84 theorems, 2 inductives, 2 recursors, 8 constructors), sanity supplement, one positive and five negative controls passed their stated expectations. Allowed transitive axioms only: propext, Classical.choice, Quot.sound. Mathematical Lean sources are byte-identical to the frozen input. Endpoint: MathDB378395.Main.collapsing_conjecture_false. Receipts: replay-receipts/result.json and all-receipts.json.

All eight PDF pages rendered and individually inspected; QA receipt: qa/QA.json. Replay used systemd MemoryMax=6G. Peak sampled private RSS 2,150,043,648 bytes; total VmRSS 4,324,327,424 bytes; longest subprocess 15.795 seconds. Caps and commands are recorded per subprocess. All launched jobs completed.

Integrity: all 1,182 frozen input files hash-identical before/after. Unrelated r73 material was not included in the dossier. Source-only archive has no compiled Lean artifacts. The full dossier adds the PDF, source copies, raw MathDB line, prior-art evidence, labelled reviewer supplements, historical and fresh receipts, QA renders and manifests. archive-hashes.json binds both archives. See REPRODUCE.md for portable replay and the trust boundary.

Novelty limitations: Schröter's 2017/2018 enumeration is the closest computational prior art; no explicit older orbit/cell representative was matched. The independent reviewers' HOLD and root's bounded qualified pass are retained separately. The tropical bridge is expository, not a priority claim. Rinaldo's exact restatement and the reviewed Fienberg–Rinaldo passages are distinguished from the Dobra later-open report, which is inherited from adjudication without a primary-body copy. Cached dependency oleans are trusted, not rebuilt.

DRAFT; zero accepted credit; root alone accepts. Campaign count remains 11/20 beyond 39 unchanged. No git, browser, external messages, publication, upload, shared ledger or other-lane edits; no child agents.
''')
# Full archive omits only reproducible installation/extraction workspaces and its own self-referential outputs.
exclude_dirs={'local-deps','fresh-extraction','full-dossier-verification','__pycache__'}
exclude_names={'full-dossier.zip','dossier-manifest.json','archive-hashes.json','full-dossier-verification.json'}
files=[p for p in D.rglob('*') if p.is_file() and not (set(p.relative_to(D).parts)&exclude_dirs) and p.name not in exclude_names and p.name not in {'finalize.log','finalize.receipt.json'}]
manifest={str(p.relative_to(D)):sha(p) for p in sorted(files)}
(D/'dossier-manifest.json').write_text(json.dumps(manifest,indent=2))
with zipfile.ZipFile(D/'full-dossier.zip','w',zipfile.ZIP_DEFLATED) as z:
 for p in sorted(files+[D/'dossier-manifest.json']):z.write(p,str(p.relative_to(D)))
# Safe extractor independently validates the final archive paths and fresh extracted bytes.
subprocess.run([__import__('sys').executable,'-I',str(D/'safe_extract.py'),str(D/'full-dossier.zip'),str(D/'full-dossier-verification')],check=True)
F=D/'full-dossier-verification'
assert all(sha(F/n)==h for n,h in manifest.items())
(D/'full-dossier-verification.json').write_text(json.dumps({'status':'PASS','members_verified':len(manifest),'fresh_safe_extraction':True,'full_zip_sha256':sha(D/'full-dossier.zip')},indent=2))
(D/'archive-hashes.json').write_text(json.dumps({n:sha(D/n) for n in ['source-only-proof.zip','full-dossier.zip']},indent=2))
print('FINAL PASS: frozen inputs, literal sources, source ZIP, full ZIP, replay, QA; zero running jobs.')
