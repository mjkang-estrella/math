from pathlib import Path
import json,hashlib,zipfile,datetime,os
r=Path(__file__).resolve().parent
h=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
load=lambda n:json.loads((r/n).read_text())
def save(n,v):(r/n).write_text(json.dumps(v,indent=2)+'\n')
v=load('receipts/replay-summary.json');a=load('receipts/audit-parse.json');bind=load('receipts/bindings.json');assert v['passed'] and a['passed'] and bind['all_bound_inputs_unchanged']
assert load('receipts/pdf-qa.json')['pdf_sha256']==h(r/'paper/edgepattern-draft.pdf')
assert load('receipts/extraction.json')['zip_sha256']==h(r/'edgepattern-source-only.zip')
# Full ZIP contains no compiled cache; validation receipts are retained in full.
results={'status':'DRAFT_READY_FOR_ROOT_REVIEW','mathdb_id':342414,'accepted_credit':0,'endpoint':'EdgePattern.TreeModelsR5.refutation : ¬ EdgePattern.Conjecture2.{0}','paper_pages':6,'formal_files_byte_identical_to_r5':274,'proof_closure_modules':268,'build_modules':269,'fresh_replay':v,'audit_parse':a,'frozen_bindings':bind,'ordinary_math':load('receipts/ordinary-math.json'),'pdf_qa':'receipts/pdf-qa.json','archives':['edgepattern-source-only.zip','edgepattern-full-dossier.zip'],'trust_limits':['Pinned precompiled external mathlib cache trusted, not rebuilt or source-attested','Universe-zero endpoint; depth-at-most robustness is ordinary mathematics','Final SIAM body, heuristic body, edge/vertex-coloured thesis body and MathDB comments unread','Inherited bounded prior-art gate, no new live registry refresh or priority claim'],'interrupted_attempt':'receipts/interruption.json; superseded, no oleans reused','root_remaining':['Independent root fresh replay and audit parse','Paper review','Registry refresh and acceptance decision']}
save('results.json',results)
(r/'SUMMARY.md').write_text(f'''# MathDB 342414: draft manuscript and Lean dossier

Ready for root review; zero accepted credit. All work is confined to edgepattern-manuscript-r1.

The six-page AI-assisted DRAFT, **A cubic counterexample to edge-pattern convex domination**, gives the exact source definitions and Conjecture 2, the eight-vertex pattern and its five maximum independent sets, the human classification into 81 labeled leaf-count forms, a closed expectation formula and exact table, and the full convex-separation proof. It states the universe-zero endpoint, formal correspondence and bridge-based classification architecture, trust and access limits, and bibliography. The unique shallower form has value 28/27; that convention robustness is ordinary mathematics, not Lean. The source optimizing vector has value 119/110 on P, while Lemma 10’s objective is 30/11; no colouring-bound claim is made.

Deliverables:

- paper/edgepattern-draft.pdf, paper/manuscript.md and paper/build.py (with fonts).
- PROOF.md, STATEMENT-CORRESPONDENCE.md, REPRODUCE.md and pins.json.
- formal/: all 274 modules byte-identical to edgepattern-formal-r5/formal. The endpoint closure has 268 modules and imports no Audit module. The build adds AuditR5; historical auditors remain outside it.
- edgepattern-source-only.zip: final hash-bound sources, portable resumable driver, full auditor, false controls and manuscript sources; no oleans.
- edgepattern-full-dossier.zip: sources, immutable evidence copies, review/adjudication records, fresh replay logs and resource receipts, QA images and manifests; no compiled caches.
- sources/342414.jsonl and its hash; source version/thesis/citing-body copies and access receipts under evidence/.
- SOURCE-MANIFEST.json, INPUT-COPY-MANIFEST.json, MODULE-HASHES.json, DOSSIER-MANIFEST.json, archive-hashes.json and receipts/.

Final replay: PASS from a safe new extraction of the final source-only ZIP. There were 269 strict -j1 warning-as-error builds and 269 one-module leanchecker calls. The full audit parsed {a['declarations']} declarations and {a['expression_nodes']} expression nodes, with no forbidden axioms, unsafe or partial declarations. Only propext, Classical.choice and Quot.sound are allowed. Auditor generated-declaration safety passed. All five false Lean controls failed by ordinary errors; existing-olean refusal passed. {v['guarded_calls']} guarded calls respected the resource caps, with peak sampled private RSS {v['peak_sampled_private_rss_bytes']} bytes and longest call {v['longest_guarded_call_seconds']:.3f} seconds. No call was resource-killed. The driver prints a final PASS line; see receipts/replay-driver.log.

An earlier long-lived outer shell exited 143 before finishing. Its partial logs are retained transparently under interrupted-replay/logs and receipts/interruption.json; it is not a PASS. The final replay restarted every module with no olean reuse and used short one-process steps, each validated against frozen source hashes. REPRODUCE.md explains the step interface.

All {bind['count']} frozen inputs match before/after bindings; both specified r5 archive hashes and EDGE-PROOF.md match TASK.txt. Every final PDF page was rendered and visually inspected. A fresh independent all-subset enumeration agrees with the closed formula at all 81 forms. No git, child agents, shared-ledger edits, browser, external messages, publication or uploads were used. No launched job remains running at handback.

Root alone accepts and must still perform its final replay, paper read, audit parse and registry refresh. Prior-art evidence remains bounded, with the unread final SIAM body and other access limits disclosed. No historical priority or exhaustive literature coverage is asserted.
''')
# Check no launched subprocess still has its cwd in this lane (except this packager).
remaining=[]
for proc in Path('/proc').iterdir():
 if not proc.name.isdigit() or int(proc.name)==os.getpid():continue
 try:
  cwd=(proc/'cwd').resolve();cmd=(proc/'cmdline').read_bytes().replace(b'\0',b' ').decode(errors='replace')
  if cwd.is_relative_to(r) and any(s in cmd for s in ['lean ','leanchecker','watchdog.py','replay.py']):remaining.append({'pid':proc.name,'cmd':cmd})
 except OSError:pass
assert not remaining,remaining
save('receipts/handback.json',{'utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'launched_jobs_remaining':remaining,'accepted_credit':0,'root_review_required':True})
exclude={'edgepattern-full-dossier.zip','DOSSIER-MANIFEST.json','archive-hashes.json','receipts/archive-integrity.json'}
files=[]
for f in sorted(r.rglob('*')):
 if not f.is_file():continue
 rel=f.relative_to(r);name=str(rel)
 if name in exclude or f.suffix in ['.olean','.ilean','.pyc'] or '__pycache__' in rel.parts:continue
 if rel.parts[0] in ['fresh-replay','interrupted-replay'] and len(rel.parts)>1 and rel.parts[1] not in ['logs','replay-receipt.json','replay-state.json','negative-results.json','auditor-safety-receipt.json']:continue
 files.append(f)
m={str(f.relative_to(r)):h(f) for f in files};save('DOSSIER-MANIFEST.json',m)
with zipfile.ZipFile(r/'edgepattern-full-dossier.zip','w',zipfile.ZIP_DEFLATED) as z:
 for f in files+[r/'DOSSIER-MANIFEST.json']:z.write(f,f.relative_to(r))
checks={}
for name in ['edgepattern-source-only.zip','edgepattern-full-dossier.zip']:
 with zipfile.ZipFile(r/name) as z:
  assert z.testzip() is None
  manifest=json.loads(z.read('SOURCE-MANIFEST.json' if name.startswith('edgepattern-source') else 'DOSSIER-MANIFEST.json'))
  assert all(hashlib.sha256(z.read(p)).hexdigest()==sha for p,sha in manifest.items())
  assert not any(p.endswith(('.olean','.ilean','.pyc')) for p in z.namelist())
  checks[name]={'sha256':h(r/name),'members':len(z.namelist()),'manifest_verified':True,'no_compiled_cache':True}
save('archive-hashes.json',{n:v['sha256'] for n,v in checks.items()});save('receipts/archive-integrity.json',checks)
print('PASS: dossier packaged, ZIP manifests verified, no running replay jobs')
