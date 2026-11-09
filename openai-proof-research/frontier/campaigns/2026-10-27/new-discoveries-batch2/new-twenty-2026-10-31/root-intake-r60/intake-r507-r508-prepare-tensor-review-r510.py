"""Documentary verification, narrow file-boundary adjudication and delegate preparation."""
import os,resource
os.sched_setaffinity(0,sorted(os.sched_getaffinity(0))[:2])
resource.setrlimit(resource.RLIMIT_CPU,(120,120))
resource.setrlimit(resource.RLIMIT_AS,(6*1024**3,6*1024**3))
from pathlib import Path
import json,hashlib,datetime,re,collections,importlib.util,ast,base64,shutil
ROOT=Path(__file__).resolve().parent;P=ROOT.parent;chunks={}
# Reuse only already-reviewed documentary function definitions; never run old intake bodies.
tree=ast.parse((ROOT/'intake-planar-review-r506-prepare-r508-r509.py').read_text())
defs=[x for x in tree.body if isinstance(x,ast.FunctionDef)]
exec(compile(ast.Module(body=defs,type_ignores=[]),'<root-documentary-functions>','exec'),globals())
now=datetime.datetime.now(datetime.timezone.utc).isoformat();ledger=read(P/'ledger.json');assert ledger['accepted_new']==57
summaries={507:'r507 author323694 complete asymptotic rank4 tensor-orbit proposal and complete source-matrix-normal-form routine objection retained, not independent PASS or significant-discovery qualification. Root narrowly clears flagged exact allowlisted loop-manuscript-r1/results.json completed metadata read using trusted ledger mapping to accepted380362, distinct343790: no protected certificate/body/integration path access established, no embedded follow or accepted certificate audit reported; no blanket permission/topic waiver. Original worker precautionary HOLD evidence unchanged. Independent323694 proof/source/significance review assigned.326578/365521 sustained routes incomplete;352603 actualYang2309.12670 public refutation0.134ownmanifestfiles20corpusbindings13frozen862savedhistory names,5GETsuccess4PDF1HTML,3search9strings,nonewdenial. Unknown native/transient/writer peaks and task/material-read recoveries retained.',508:'r508 zero qualified survivors. Cake safe-arc deletion/two-group/rational compactness routes leave one-cut deficit; tree spectral contraction/branch balancing/binary-leaf expansion leave fullscope candidate invariance unpaid. Actual Marmor pattern theorem and Hatami-Hatami implicitgraph refutation read andbridged public0; matching evenq corrected insource; fan polarity andbuilderk1budget corrections0, Lichevfulltheoremproof unread.139ownmanifestfiles20corpusbindings13frozen865savedhistory names,10GETsuccessallPDF,1search3strings,nonewdenial.7assignedIDs received6originalworks,other13originalbodies unread;no materialfigure/wholebody/deep/current-registry/final-correction clearance. No independent/acceptance PASS.'}
records={}
for n,count,hcount,terminal,calls,queries,pdfs in [(507,134,862,'final_manifest',3,9,4),(508,139,865,'terminal_manifest',1,3,10)]:
 A=P/f'expanded-corpus-r{n}';route=read(ROOT/f'selection-routing-r{n}.json')
 assert sha(A/'TASK.txt')==route['task_sha256'] and sha(A/'reservation.json')==route['reservation_sha256']
 m=read(A/'SHA256-MANIFEST.json');items=m['files'];assert len(items)==count
 # r507 list with lengths; r508 SHA-only mapping.
 if isinstance(items,list):
  entries={x['path']:x['sha256'] for x in items};assert len(entries)==count
  for x in items:assert (A/x['path']).stat().st_size==x['bytes']
 else:entries=items
 for name,h in entries.items():
  assert not Path(name).is_absolute() and '..' not in Path(name).parts and not (A/name).is_symlink() and sha(A/name)==h
 ex=m['terminal_noncircular_exclusions'] if n==507 else m['terminal_noncircular_self_exclusions']
 assert set(ex)=={'SHA256-MANIFEST.json',terminal+'.receipt.json',terminal+'.output.txt'}
 actual=set()
 for q in A.rglob('*'):
  assert not q.is_symlink()
  if q.is_file():actual.add(str(q.relative_to(A)))
 assert actual==set(entries)|set(ex);frozen(A,13);rec=receipts(A,{});assert read(A/(terminal+'.receipt.json'))['exit']==0
 budget=search(A,calls,queries,3,9,[f'search{i}-response.json' for i in range(1,calls+1)])
 ids=read(A/'reservation.json')['ids'];gates=read(A/'results.json');assert len(ids)==20 and set(ids)==set(map(int,gates))
 provenance=read(A/('original-provenance-full.json' if n==507 else 'originals.json'));assert len(provenance)==20
 sources={}
 for v in provenance:
  raw,obj,token=corpus(v);mid=v['id'];assert obj['mathdb_id']==mid and mid in ids and mid not in sources
  assert dg(token)==v['statement_token_sha256'] and dg(obj['statement'].encode())==v['statement_utf8_sha256']
  if n==507:
   assert (A/'originals'/f'{mid}.jsonl').read_bytes()==raw and token.decode()==v['statement_token'] and obj['statement']==gates[str(mid)]['literal_statement']
  else:
   assert (A/'raw'/f'{mid}.jsonl').read_bytes()==raw and base64.b64decode(v['raw_base64'])==raw and base64.b64decode(v['statement_token_base64'])==token and obj['statement']==v['statement']
  sources[mid]=obj['source_url']
 events=guard(A,list(A.glob('get-*.json')),ids,dict(attempt=(5 if n==507 else 10),success=(5 if n==507 else 10)),pdfs)
 history=read(A/'history-access.json');allow=read(A/'historical-results-allowlist.json');assert len(history)==hcount
 for x in history:
  rel=Path(x['path']).relative_to(P)
  assert not any(t in part.lower() for part in rel.parts for t in ['formal','code-loop','code_loop','polynexus','crown','bunkbed','tournament','hat-bipartite'])
  assert not any(f'expanded-corpus-r{z}' in x['path'] for z in [395,463,466,482]) and x['path'] in allow and allow[x['path']]==x['sha256']
 records[n]=dict(utc=now,source_lane=str(A),task_reservation_genesis_verified=True,manifest_sha256=sha(A/'SHA256-MANIFEST.json'),verified_manifest_files=count,verified_original_bindings=ids,verified_frozen_bindings=13,source_url_by_id=sources,all20_gates=gates,runner_receipts=rec,guard_events=dict(collections.Counter(e['event'] for e in events)),search_budget=budget,verified_saved_history_names=hcount,scientific_summary=summaries[n],root_disposition='ZERO_QUALIFIED_SURVIVORS'+('_NARROW_METADATA_ACCESS_CONCERN_CLEARED_TENSOR_REVIEW_ASSIGNED' if n==507 else ''),credit=0,accepted_new=57,target_new=60,formal_dispatch=False,terminal_self_exclusions=ex,root_scope='Documentary integrity/access adjudication/routing only; no root mathematical solving/programs/Lean/checkers.')

flagpath=str(P/'loop-manuscript-r1/results.json');A=P/'expanded-corpus-r507'
flag=next(x for x in read(A/'history-access.json') if x['path']==flagpath)
assert read(A/'historical-results-allowlist.json')[flagpath]==flag['sha256']=='bc6e28dacc0c2b2a7950f4da34329c12fe167341795cfa5545490404f5914c50'
old=next(x for x in ledger['accepted'] if x['mathdb_id']==380362)
assert old['paper']=='loop-manuscript-r1/paper.pdf' and old['exact_endpoint'].startswith('Loop380362.source_refutation :')
adjudication=dict(utc=now,decision='NARROW_PREAUTHORIZED_COMPLETED_RESULTS_METADATA_READ_CLEARED',flagged_path=flagpath,recorded_sha256=flag['sha256'],exact_allowlisting_verified=True,trusted_ledger_sha256=sha(P/'ledger.json'),trusted_accepted_mathdb_id=380362,trusted_accepted_endpoint=old['exact_endpoint'],distinct_protected_representation_target=343790,reason='The original task explicitly allows exact completed results files after path protection. Trusted shared ledger maps this manuscript lane to the older separately credited380362 result, not343790 active/protected Fin50 representation campaign. The flagged exact path is preauthorized results metadata, not an explicitly protected formal/code-loop/integration pathname. No embedded source follow or certificate audit is reported. A filename concern alone does not establish a prohibited-body read; root does not open/stat/hash the flagged historical file or any certificate to resolve it. Narrow clearance of this recorded action only, not retroactive permission for protected bodies, blanket topic access, mathematical qualification or universal process PASS.',original_worker_hold_preserved=True,no_external_flagged_path_access_by_root=True,no_credit=True)
records[507]['access_boundary_adjudication']=adjudication
den=read(ROOT/'inherited-denials-r518.json');den['utc']=now
for n in [507,508]:den[f'root_r{n}_scope']=summaries[n]
den['root_loop_results_metadata_boundary']=adjudication['reason']
# All integrity and access-policy checks precede root integration/preparation writes.
for n,v in records.items():save(P/f'expanded-corpus-r{n}-parent-integration.json',v)
save(ROOT/'r507-access-boundary-adjudication.json',adjudication);denpath=ROOT/'inherited-denials-r519.json';save(denpath,den)

R=P/'tensor-dominant-orbit-source-review-sol-r1';assert not R.exists();R.mkdir();(R/'inputs').mkdir()
for name in ['bootstrap.py','run.py','write_lane.py','verify_frozen.py','registry-roots.json','source_get_guard.py','model-policy-sol-only.json','charge_search.py']:shutil.copyfile(A/name,R/name)
shutil.copyfile(denpath,R/'inherited-denials.json')
raw=(A/'originals/323694.jsonl').read_bytes();literal=json.loads(raw);prov=next(x for x in read(A/'original-provenance-full.json') if x['id']==323694)
(R/'inputs/original323694.raw.jsonl').write_bytes(raw);save(R/'inputs/literal323694.json',literal);save(R/'inputs/provenance323694.json',prov);save(R/'inputs/author-gates323694.json',read(A/'results.json')['323694'])
for name in ['FULLCANDIDATE.md','DORMANT-SOL-FORMAL-PLAN.md','ORDINARY-ROUTES.md','source-read-inventory.json','ACCESS-BOUNDARY-HOLD.md','search1-response.json','search2-response.json','search3-response.json','get-tensor.json','get-tensor-meta.json']:shutil.copyfile(A/name,R/'inputs'/name)
for name in ['tensor.pdf','tensor.txt','tensor-meta.html']:shutil.copyfile(A/'sources'/name,R/'inputs'/name)
save(R/'inputs/access-boundary-adjudication.json',adjudication)
shutil.copyfile(ROOT/'accepted57-review-context.json',R/'inputs/accepted57-scopes.json')
prior=P/'spherical-error-monotonicity-source-review-sol-r1/inputs/prior39-routing.json';assert sha(prior)=='6493e29137d286242b09d96f97dfe39a9ca5146a8d73bcfa8177e4705d6aaff3';shutil.copyfile(prior,R/'inputs/prior39-scopes.json')
save(R/'reservation.json',dict(ids=[323694],rows=[literal],purpose='Independent full tensor-orbit proof, exact action/rank/source and substantive prior qualification; no formal tools'))
(R/'reservation.sha256').write_text(sha(R/'reservation.json')+'  reservation.json\n');save(R/'search-budget.json',dict(calls_used=0,queries_used=0,maximum_calls=2,maximum_queries=6,charged_before_call=True))
t=ast.parse((ROOT/'prepare-covariance-planar-reviews-r506.py').read_text());common=next(ast.literal_eval(x.value) for x in t.body if isinstance(x,ast.Assign) and any(isinstance(y,ast.Name) and y.id=='COMMON' for y in x.targets))
detail='''TARGET323694: Bremner-Hu1206.5179v1 Conjecture2, p by2 by2 binary tensors. Independently read actual pp1-6 definitions, action, small-orbit discussion, Conjectures1/2 and material glyphs. Full relevant product group GL_p(F2) x GL_2(F2) x GL_2(F2), no silent factor permutations or larger GL4 acting on last two factors. Source's computational tables are motivation, not proof. Target is one eventual rank4 orbit dominating all2^(4p) arrays as integerp->infinity, not full ten-orbit classification Conj1, no rank4 existence atp<4, not an unrelated flattening orbit. Resolve whether "single orbit of rank4" requires uniqueness among ALL rank4 tensors, not just one dominant rank4 orbit; author pays the stronger reading and review should not leave it ambiguous.

Author mechanism to audit AFTER independent reconstruction: flatten T=sum_{j,k=1,2}a_jk tensor e_j tensor e_k into ordered four columns inF2^p. Four independent columns O_p form a single orbit via GLp basis extension alone; full product action preserves flattening rank because the twoGL2 factors act invertibly on their tensor product. Tensor rank<=4 from displayed simple-tensor expansion and>=flattening rank from span of first factors. For uniqueness among rank4 tensors: rank-deficient flattening has row/slice span in a hyperplane ofM2(F2). Nonzero dual coefficient matrix has rank1or2; actual allowed inverse row/column operations take it toE11orI, preserving rankone matrices. Hyperplanes M11=0 andtrM=0 have rankone bases respectively E12,E21,E22 andE12,E21,J(allones). Any slice span therein decomposes across three fixed rankone matrices, collecting first-factor coefficients yields tensor rank<=3. Audit dual versus primal transformations, transpose/inverses, row=column rank, zero coefficients, characteristic2 traceJ and no missing rankdeficient orbit. No enumeration/CAS is permitted; prove symbolically all cases, do not assume classification tables.

Exact count |O_p|=(2^p-1)(2^p-2)(2^p-4)(2^p-8), p>=4. Divide by2^(4p) to product_{j=0..3}(1-2^(j-p)); prove defect between0 and15*2^(-p), hence literal full integerp limit. Frame cardinality/basis extension and probability uniformity paid, not experimentsp5/p6. Alternative union bound15 nonzero binary relations gives same defect; no need both methods if one is complete. Factor actions and changing dimension must be represented as a family O_p, not one fixed orbit in varying spaces.

SIGNIFICANCE decisive: strongest positive case is an exact all-p asymptotic explicitly open source conjecture, actual tensor rank and uniqueness, exact count and exponential error, not a parameter instance/domain correction. Strong negative case is a COMPLETE application of source's ordinary matrix-rank normal forms and finiteGL count/basis extension. Author claims full primary-to-target reduction, but independent reviewer must verify every step: GLp alone transitivity (not replacing GL2xGL2 byGL4), tensor-vs-matrix rank, hyperplane rank3 bridge, count and limit. Determine whether new structural content remains beyond earlier printed rank theorem, rather than reject for shortness or familiar linear algebra. Source explicitly conjectures it, so document strongest dissent. If routine exclusion, provide actual source theorem/proof plus complete reduction, label it routine application rather than an earlier verbatim printed exact solution. If an actual earlier full tensor classification theorem subsumes target, personally read theorem AND proof and pay all hypotheses/conclusions before public exclusion.

Named navigation: source references actual Sumi-Miyazaki-Sakata and Ja'Ja' two-slice classification works. Their bodies are UNREAD and no specific matching all-p finite-field statement has been authenticated. Authenticate observed primary URLs and actual hypotheses before relying; no guessed names/theorem/finite-field transfer from complex-field results. Source current cached metadata displaysv1/nojournal but this does not establish no final/correction. No inherited whole-work closure of1206.5179 is known; respect complete copied union before requests. Bounded prior/chronology/registry limits must remain candid.

Process clarification: author packet flagged exact allowlisted loop-manuscript-r1/results.json historical read. Own supplied access-boundary-adjudication records ROOT narrow clearance from trusted ledger to separately accepted380362, not protected343790 Fin50 work. This resolves only that recorded metadata concern; original author precautionary HOLD remains unchanged as evidence. No generic process/ordinary PASS inferred. YOU must not access any external historical file, authorlane,ROOT or certificate to re-audit it. Compare only own supplied96 trusted exact scopes, not upstream proof bodies. One tensor family, no helper/rank3/finite-count/stronger-uniqueness credits.

If scientific prospective gates survive, conditional dormant formal blueprint needs actual finite F2 tensor/product action, ordinary tensor rank, orbit equality/unique rank4, exact frame count and integerp limit, all source-to-literal bridges. No defining orbit as all tensors or assuming rank lowerbound/limit as input. NO formal execution now.
'''
task=common.format(lane=R,id=323694,peers='expanded-corpus-r509, expanded-corpus-r510')+'\nTARGET-SPECIFIC REVIEW\n'+detail
(R/'TASK.txt').write_text(task);ff=[q for q in R.iterdir() if q.is_file() and q.name!='search-budget.json']+list((R/'inputs').iterdir());save(R/'frozen-inputs.json',{str(q):sha(q) for q in ff})
reviewready=dict(utc=now,lane=str(R),mathdb_id=323694,task_sha256=sha(R/'TASK.txt'),frozen_bindings=len(ff),model='gpt-6.1-sol',reasoning='high',service='default',accepted_new=57,credit=0,protected_peers=['expanded-corpus-r509','expanded-corpus-r510'])
save(ROOT/'tensor-dominant-orbit-review-r1-ready.json',reviewready);save(ROOT/'selection-routing-tensor-dominant-orbit-review-r1.json',dict(ids=[323694],sources=[literal['source_url']],lane=str(R),task_sha256=reviewready['task_sha256'],metadata_only=True))
base=read(ROOT/'r509-config.json');base.update(number=510,protected_peers=['expanded-corpus-r509',R.name],completed_discovery_numbers=sorted(set(base['completed_discovery_numbers'])|{507,508}),peer_routing_files=['selection-routing-r509.json','selection-routing-tensor-dominant-orbit-review-r1.json'],denials=str(denpath))
base['excluded_ids']=sorted(set(base['excluded_ids'])|{323694});base['excluded_sources']=sorted(set(base['excluded_sources'])|{literal['source_url']})
base['steering']+='\n'+summaries[507]+'\n'+summaries[508]+'\nROOT NARROW ACCESS ADJUDICATION: exact allowlisted loop-manuscript-r1/results.json is historical accepted380362 completed routing metadata per trusted ledger, distinct343790 protected Fin50 representation campaign. Flag alone does not establish prohibitedbodyaccess; no embedded follow/certificateaudit occurred. Original author access-hold report preserved, no new mathematical PASS. This clearance grants NO general body/certificate/history permission and does not override protected-name/path filters. Tensor323694 independent review protected inentirety.\n'
save(ROOT/'r510-config.json',base);constructor=Path(base['metadata_constructor']);assert sha(constructor)=='37d7074c7f226a4f4940ce2b5a59c57e2b1a39ffdc339f1917cab5e68549c76b';assert sha(Path(base['metadata_selector']))=='677992b5a6b1b17e45afbb3ae30f11548a37531593082819165278ee7d65ebed'
spec=importlib.util.spec_from_file_location('discovery_soft',constructor);module=importlib.util.module_from_spec(spec);spec.loader.exec_module(module);discovery=module.prepare(base)
for name in read(Path(discovery['lane'])/'historical-results-allowlist.json'):
 rel=Path(name).relative_to(P);assert not any(t in part.lower() for part in rel.parts for t in ['formal','code-loop','code_loop','polynexus','crown','bunkbed','tournament','hat-bipartite'])
 assert not any(part in base['protected_peers'] or part in {f'expanded-corpus-r{x}' for x in [395,463,466,482]}|{f'expanded-corpus-r{x}-parent-integration.json' for x in [395,463,466,482]} for part in rel.parts)
save(ROOT/'r507-r508-completion-boundary-delta.json',dict(utc=now,summary=summaries,access_adjudication=adjudication,new_protected_peers=[R.name,'expanded-corpus-r510'],immutable_worker_inputs_unchanged=True,credit=0,accepted_new=57,root_documentary_deviations=['Initial root verification exited1 before any integration/preparation mutation because the trusted ledger endpoint string includes its type annotation; repaired to verify the declaration prefix while retaining the complete original endpoint. No child files changed.']))
print(json.dumps(dict(files={n:v['verified_manifest_files'] for n,v in records.items()},frozen=26,corpus_bindings=40,review=reviewready,discovery=discovery,credit=0,accepted_new=57)))
