"""Root documentary intake and hypothesis-review packet construction only."""
import os,resource
os.sched_setaffinity(0,sorted(os.sched_getaffinity(0))[:2])
resource.setrlimit(resource.RLIMIT_CPU,(120,120));resource.setrlimit(resource.RLIMIT_AS,(6*1024**3,6*1024**3))
from pathlib import Path
import json,hashlib,datetime,collections,re,shutil
P=Path(__file__).resolve().parent.parent;ROOT=P/'root-intake-r60';A=P/'expanded-corpus-r469';R=P/'lr-translation-degree-source-proof-review-sol-r1'
def sha(q):return hashlib.sha256(q.read_bytes()).hexdigest()
def dg(b):return hashlib.sha256(b).hexdigest()
def save(q,v):
 assert not q.exists(),str(q)
 q.parent.mkdir(parents=True,exist_ok=True);q.write_text(json.dumps(v,indent=2)+'\n')
now=datetime.datetime.now(datetime.timezone.utc).isoformat();assert json.loads((P/'ledger.json').read_text())['accepted_new']==57
routing=json.loads((ROOT/'selection-routing-r469.json').read_text());assert sha(A/'TASK.txt')==routing['task_sha256'] and sha(A/'reservation.json')==routing['reservation_sha256']
manifest=json.loads((A/'byte-manifest.json').read_text());entries={x['path']:x for x in manifest['files']};assert len(entries)==197
for n,v in entries.items():
 assert not Path(n).is_absolute() and '..' not in Path(n).parts
 q=A/n;assert not q.is_symlink() and sha(q)==v['sha256'] and q.stat().st_size==v['bytes'],n
exclusions=manifest['terminal_noncircular_self_exclusions'];assert {str(q.relative_to(A)) for q in A.rglob('*') if q.is_file()}==set(entries)|set(exclusions)
frozen=json.loads((A/'frozen-inputs.json').read_text());assert len(frozen)==13 and all(Path(n).parent==A and sha(Path(n))==h for n,h in frozen.items())
after=json.loads((A/'frozen-after.json').read_text());assert after['count']==13 and after['mismatches']==[]
reservation=json.loads((A/'reservation.json').read_text());ids=reservation['ids'];gates=json.loads((A/'results.json').read_text());prov=json.loads((A/'literal-provenance.json').read_text());assert len(ids)==20 and set(ids)==set(map(int,gates))=={x['id'] for x in prov}
chunks={};source_by_id={}
for row in prov:
 key=str(row['id']);q=Path(row['chunk']);assert q.is_relative_to(P.parent/'lanes/pi-mathdb-full-corpus-inventory-r301/corpus')
 if str(q) not in chunks:
  b=q.read_bytes();chunks[str(q)]=(dg(b),b.splitlines(keepends=True))
 h,lines=chunks[str(q)];assert h==row['chunk_sha256'];raw=lines[row['line']-1]
 assert dg(raw)==row['raw_sha256'] and row['newline'] is True and raw.endswith(b'\n') and (A/f'originals/{key}.raw.jsonl').read_bytes()==raw
 obj=json.loads(raw);assert obj['mathdb_id']==row['id'];source_by_id[key]=obj['source_url']
 token=re.search(rb'"statement"\s*:\s*("(?:[^"\\]|\\.)*")',raw)[1]
 assert dg(token)==row['token_sha256'] and (A/f'originals/{key}.token.txt').read_bytes()==token
 assert json.loads(token)==obj['statement'] and dg(obj['statement'].encode())==row['decoded_sha256'] and (A/f'originals/{key}.statement.txt').read_bytes()==obj['statement'].encode()
 assert gates[key]['acceptance_gate']['credit']==0 and not gates[key]['acceptance_gate']['accepted']
receipts=[]
for q in sorted(A.glob('*.receipt.json')):
 v=json.loads(q.read_text());assert v['cwd']==str(A) and v['cpu_limit_s']==115 and v['as_limit_bytes']==6*1024**3 and v['deadline_s']==130
 receipts.append(dict(path=q.name,sha256=sha(q),exit=v['exit']))
assert json.loads((A/'terminal-manifest.receipt.json').read_text())['exit']==0
budget=json.loads((A/'search-budget.json').read_text());assert budget['calls_used']==3 and budget['queries_used']==9
charges=[json.loads(s) for s in (A/'search-charges.jsonl').read_text().splitlines()];assert len(charges)==3
previous=dict(calls_used=0,queries_used=0,maximum_calls=3,maximum_queries=9,charged_before_call=True)
for i,c in enumerate(charges,1):
 assert c['sequence']==i and c['before']==previous and sha(A/c['plan'])==c['plan_sha256'] and json.loads((A/c['plan']).read_text())['queries']==c['queries']
 expected=dict(previous);expected['calls_used']+=1;expected['queries_used']+=len(c['queries']);assert c['after']==expected;previous=expected
 assert json.loads((A/f"search-{['one','two','three'][i-1]}-full.json").read_text())
assert previous==budget and sha(A/'charge_search.py')==sha(ROOT/'charge_search.py')
events=[json.loads(s) for s in (A/'guard-ledger.jsonl').read_text().splitlines()];counts=collections.Counter(e['event'] for e in events);assert counts==dict(attempt=8,success=8)
for e in events:
 if e['event']=='success':assert sha(A/e['destination'])==e['sha256'] and (A/e['destination']).stat().st_size==e['bytes']
history=json.loads((A/'historical-access-inventory.json').read_text());assert len(history)==768;forbidden=('formal','code-loop','polynexus','crown','bunkbed','tournament','hat-bipartite')
assert all(not any(t in part.lower() for t in forbidden) for x in history for part in Path(x['path']).relative_to(P).parts)
quality=json.loads((A/'quality-check.json').read_text());assert quality['historical_access_audit_prohibited_count']==0 and quality['qualified_survivors']==0 and quality['formal_dispatches']==0
record=dict(utc=now,source_lane=str(A),manifest_sha256=sha(A/'byte-manifest.json'),verified_manifest_files=197,verified_original_bindings=sorted(ids),verified_frozen_bindings=13,source_url_by_id=source_by_id,routing_pins='Actual task/reservation hashes match retained ROOT genesis',runner_receipts=receipts,receipt_exit_counts=dict(collections.Counter(str(x['exit']) for x in receipts)),guard_events=dict(counts),search_budget=budget,search_counter_continuity='Live old/new states, exact plan digests/querystrings, final counter/helper authenticated; full saved responses parsed',root_disposition='ZERO_QUALIFIED_SURVIVORS_318479_CONDITIONAL_ROUTE_ASSIGNED_INDEPENDENT_INVESTIGATION',scientific_summary='320587sourceproposedtruncatedsimplexlowerconstruction/sizepaid, fullupper/equality simultaneousfiberdeficit unpaid.318479source eventualpolynomiality alreadypublic, exactdegree preservation conditionalpolytopegrowth route promising but actualfixedhive/tableaulatticeencoding/boundedness/allboundarydimensiondegree/priorbridgesunpaid; no authorordinaryfullPASS.318895/318896Eisenstein representation equivalence/gluing/reconstruction gaps; realisometry notcomplexHermitianpreservation, partialconjugation boundarycompatibility unpaid, Gramconjugationbarsnotvisuallyverified.317704actualWang0809.1604sourceownfull0;316577actualWoodroofe0708.3539v3Th4.1/Prop4.3sourceownfull0;318272actualChebotarev2610.14100v3Lemmas7-8Th9analyticalln5refutation complete primaryscopebridge0, no numericalfigurecertificate reliance.318033precedinginitialmomentdisplayforcescorrection0, actualGesselKim1003.5301corrected2distantproofread; corrected3distantproofspecificallyunread. Thirteenreservedoriginalsunread.',all20_gates=gates,new_denials=False,history_access_audit=dict(saved_records=768,protected_component_matches=0,scope='Ownsavedinventory only, no historical externalpaths followed byroot'),process='No reported localfailedinvocations or newsourceunavailability; fullsavedoutputs/materialrecoveries retained. No visualfigures claimed. Sampled/native/writerpeak limits retained, no universalcompliance assertion.',root_scope='Documentary integrity/routing only; no root mathematical solving/programs/Lean/checkers or protected externalpathfollow',credit=0,accepted_new=57,target_new=60,formal_dispatch=False,terminal_self_exclusions=exclusions)
save(P/'expanded-corpus-r469-parent-integration.json',record)
den=json.loads((ROOT/'inherited-denials-r471.json').read_text());den['utc']=now
den['root_r469_scope']='No newdenials.320587truncatedsimplexfullupper/equality gap;318479actualhive/tableaumodel/dimensiongrowth/prior bridgesunpaid, conditionalpolytope route nowindependentlyassigned;318895/318896Eisensteinpartialconjugationgluing/reconstruction gaps, realversusHermitian distinctions.317704/316577sourceownpublictheorems0;318272actualChebotarev2610.14100v3analyticL7-8Th9alln5publicrefutation0;318033sourceinitialmomentcorrection0/corrected2distantpublicproof,3distantproofunread.197ownmanifest20originalbindings13frozenverified,8GETsuccess3search9queries;768ownsavedaccessrecords no protectedcomponents.57/60unchanged.'
denpath=ROOT/'inherited-denials-r472.json';save(denpath,den)
assert not R.exists();R.mkdir();(R/'inputs').mkdir();base=P/'expanded-corpus-r433'
for name in ['bootstrap.py','run.py','write_lane.py','verify_frozen.py','registry-roots.json','source_get_guard.py','model-policy-sol-only.json']:shutil.copyfile(base/name,R/name)
shutil.copyfile(ROOT/'charge_search.py',R/'charge_search.py');shutil.copyfile(denpath,R/'inherited-denials.json')
raw=(A/'originals/318479.raw.jsonl').read_bytes();literal=json.loads(raw);assert literal['mathdb_id']==318479
(R/'inputs/original318479.raw.jsonl').write_bytes(raw);save(R/'inputs/literal318479.json',literal);save(R/'inputs/author-gates318479.json',gates['318479'])
s=(A/'ORDINARY-ATTEMPTS.md').read_text();start=s.index('## 318479:');end=s.index('\n## 318895',start);(R/'inputs/author-route318479.md').write_text(s[start:end]+'\n')
for name in ['lr.pdf','lr.txt']:shutil.copyfile(A/'sources'/name,R/'inputs'/name)
shutil.copyfile(A/'get-lr.json',R/'inputs/get-lr.json');shutil.copyfile(ROOT/'accepted57-review-context.json',R/'inputs/accepted57-scopes.json')
prior=P/'spherical-error-monotonicity-source-review-sol-r1/inputs/prior39-routing.json';assert sha(prior)=='6493e29137d286242b09d96f97dfe39a9ca5146a8d73bcfa8177e4705d6aaff3';shutil.copyfile(prior,R/'inputs/prior39-scopes.json')
save(R/'reservation.json',dict(ids=[318479],rows=[literal],purpose='Independent full ordinary proof/source/prior/significance investigation; no formal tools or acceptance'))
(R/'reservation.sha256').write_text(sha(R/'reservation.json')+'  reservation.json\n');save(R/'search-budget.json',dict(calls_used=0,queries_used=0,maximum_calls=2,maximum_queries=6,charged_before_call=True))
task=f'''GPT-6.1 Sol high effort/default speed ONLY. Independent hypothesis-specific full ordinary proof and source/significance investigation for MathDB318479. No children/providerfallback/formal execution/selfcredit. Current57/60 beyond39 prior,96total. Root orchestrates; you do mathematics personally.

FIRST shell command EXACTLY:
timeout 20 python3 -I -B {R}/bootstrap.py
Read COMPLETE TASK/AGENTS. SECOND EXACTLY:
timeout 140 python3 -I -B {R}/verify_frozen.py before
No trailing punctuation. Bootstrap and standalone before/after verifiers are explicit capexceptions; do not nest verifiers under run.py. Every other substantive local operation must use immutable ABSOLUTE {R}/run.py with fresh label/Python stdin and immutable ABSOLUTE {R}/write_lane.py for own writes. Childcwd ownlane. Never rerun bootstrap or edit frozen inputs/helpers/caps/TASK. Preserve failures and target diagnostic repairs; ordinary local typo/serialization failure not automatically external policybreach. Actual access/protectedfile/guard/counter/cap violation means STOP/quarantine with evidence.

Your premise is NOT a proved candidate: the author supplied only a CONDITIONAL rational-polytope growth route. Independently close a complete exact ordinary proof, disprove a bridge/target, or leave an exact gap; also authenticate source scope and applicable priors and adjudicate significance. Do not return only acquisition or an acknowledgment. No mathematical programs/enumeration/numericalexperiments/CAS/solvers/Lean/compiler/checker/formalAPI. Documentary/PDF processing only under caps.

Historical access is restricted to your OWN frozen inputs/. No authorlane/ROOT/old campaign files, no embedded path follow, no old certificate audit. Active peers expanded-corpus-r470 and expanded-corpus-r471 forbidden evenmetadata/stat/read/hash/list/glob/poll. All old formal/code-loop/Polynexus/crown/bunkbed/tournament/Hat bodies and flat integrations forbidden. r463/r466 ALLoutputs/acquisitions/claims quarantined; no reuse. An old allowlist is not permission. This review intentionally has NO historicalallowlist. Trusted57+39 fullscope snapshots copied for bounded family comparison only.

Read original318479.raw.jsonl/literal JSON exactly, and actual original0904.4778 in own lr.pdf/lr.txt. Personally authenticate definitions, tuple order, size/partition conventions, all hypotheses, Lemma5.3 eventualpolynomiality, Lemma5.6 dominance subclass, and exact Conjecture5.5 degree-preservation assertion including the degreezero/Fulton eventualconstancy clause. Do not silently replace zero-polynomial degree or n0 conventions. Source title/corpus synopsis about eventualpolynomiality is weaker than the full target. Read relevant proof bodies; inspect material equation/figure pages if needed. If usingPDF announce/read /home/mj-kang/.codex/plugins/cache/openai-primary-runtime/pdf/26.1103.10131/skills/pdf/SKILL.md; no PDF authoring requested.

AUTHOR ROUTE TO AUDIT: fixed rational inequality model with parameter n*a+b, limiting direction polytope and bounded offset vertex forms might bound integerpoints by O(n^D), including boundary directions. Source addition injection supplies a lower bound; eventualpolynomiality plus an actual dimension-degree bridge might give exact degree. All of that is CONDITIONAL in the author notes. Pay the actual hive/tableau lattice-point bijection with fixed finite dimension/inequalities for all six arbitrary partitions, boundedness/normalization, rational affine-span/grid control, upper growth, identification of dimension with stretched polynomialdegree (including thin/boundary/empty cases), lower bound, and eventualpolynomial alln versus subsequences. If using Ehrhart/parametricpolytope theorems, read actual precise primary statements/proofs and give a complete applicable specialization; no unsupported model name or appeal to Hilbert polynomial. Source's dominance condition cannot be inferred on supporting faces. Do not confuse quasi-polynomial with polynomial or eventually-polynomial with exact degree preservation. Audit the conditional thickening argument for hidden recession, dimension, degeneracy, periodicity or lattice failures. If this route fails, sustain credible alternate ordinary mechanisms before parking.

SPECIFIC PRIOR LEAD, not an authenticated solution: actual earlier native search located 'Quiver generalization of a conjecture of King, Tollu, and Toumazet', JAlgebra2017 DOI10.1016/j.jalgebra.2017.03.011. Snippet says its lastsection deduces an LR result as Cor9.4, not necessarily this translateddegree claim. Investigate actual applicable theorem/proof if possible under budgets. Title/KTT ordinary-stretch identities are not automatically translation-degree results. Find actual primary hive/tableau and stability models through authenticated references or bounded search. Distinguish actual final/current/correction/prior claim, boundednonmatch and precise unreadbodyHOLD. No generic worldwideunknown veto, no no-hit novelty inference. Do not attempt alternate delivery of any work after a failed identified route. This2017 lead has not been denied merely because other papers on its host were denied.

If a complete proof closes: explicitly compare content with source own5.3/5.6, actual applicable prior results, and trusted57+39 families. A standard model plus general existing growth theorem may or may not be a routine adaptation: exclusion requires COMPLETE actual-primary-to-target bridge and strongest contrary significance case, not shortness/smallness/standardtools alone. A public exact prior earns0. A new full intended result needs substantive qualification, not an openlabel. Root alone accepts. No self-credit or formaldispatch. If ordinaryfullscope/scientific gates survive, save actual PROOF.md and a CONDITIONAL DORMANT-SOL-FORMAL-PLAN.md with exact objects/endpoints/all bridges; do not write Lean or run formal tools.

Read ENTIRE inherited-denials.json before networking, recover materialtruncations. Sole GET client immutable source_get_guard.py under run.py; ONE manually selected persisted exact plan perinvocation, fields url/routes/destination/source_identity/purpose, routes['318479'], unique new sources/destination, identity/purpose>=12chars. Maximum8GETHOPS TOTAL (redirectscharged), at most2 native searchcalls/6exactquerystrings WHOLEreview. No custom HTTP/requests/curl/wget/HEAD/nativeopen-fetch/browser/accounts/API/POST/TLS/cookie/JS/metarefresh bypass. Every failure makes identifiedwork unavailable across ALLnewhosts/versions/arxiv/authors/caches/mirrors/DOI/API/body/metadata deliveries; no retry, alternateidentitycorrection or indirectrecovery. Four registry-rootmetadata artifacts remainunavailable, no refresh/reconstruction; distinct primary publications may be read within rules. Cacheddatedheads not currentclearance.

Before EACH native search save exact queries-list plan via writer, charge using immutable ABSOLUTE charge_search.py under run.py, LIVE continuity. Never manually edit/reset/refund search-budget.json or search-charges.jsonl. Save FULL actualresponse immediately. Supported JSON/stringserialization; btoa/TextEncoderunavailable. Preserve serializationerrors and save SAME complete in-memory response before more research, without another networkcall. Searchsnippets navigationonly.

Caps:affinity<=2,childCPU115/supervisor120,AS6GiB,sampledgroupRSS6GiB,deadline130/outer140,arena2. Standalone verifierCPU120exception. True receipts/output/resources,synchronousreaping,no backgroundjobs. Allwrites OWNlane ONLY,no/tmp/parent/shared/dependency edits/git/install/publish/accounts/messages. Native/transient/writerpeak telemetry unavailable; no universal processcomplianceclaim. A normal failedGET means workunavailable, not automatically policybreach. On actual guard/policy/counter/access violation STOPnetwork/math and quarantine/preserve/report originalevidence, no resets.

Deliver REVIEW.md, PROOF.md or GAP.md, keyedreview.json for318479 with separate literal/source/ordinary/prior/novelty/significance/family/formal/independent/procedure/acceptance gates, exact source map/read/figure/access/search/resource inventories, objections and strongest contrary cases, actual receipts/hashmanifest. Final standalone frozen-after, then own terminalmanifest with every completed receiptJSON/helpers/inputs/plans/payloads/responses/guardledger/reports/frozen-after; exact named noncircular selfexclusions. No subsequent frozenwrites. Complete actual bounded hypothesis investigation; no claim fullproof from conditional deductions or acquisition. Credit0,count57/60 unchanged untilrootacceptance.
'''
(R/'TASK.txt').write_text(task);files=[q for q in R.iterdir() if q.is_file() and q.name!='search-budget.json']+list((R/'inputs').iterdir());save(R/'frozen-inputs.json',{str(q):sha(q) for q in files})
ready=dict(utc=now,lane=str(R),mathdb_id=318479,task_sha256=sha(R/'TASK.txt'),frozen_bindings=len(files),model='gpt-6.1-sol',reasoning='high',service='default',accepted_new=57,credit=0,protected_peers=['expanded-corpus-r470','expanded-corpus-r471'],source_copy_scope='Cleanr469 target-only ordinary route/literal/source; no quarantined inputs')
save(ROOT/'lr-degree-review-r1-ready.json',ready);save(ROOT/'selection-routing-lr-degree-review-r1.json',dict(ids=[318479],sources=['https://arxiv.org/abs/0904.4778'],task_sha256=ready['task_sha256'],lane=str(R),metadata_only=True))
print(json.dumps(dict(accepted_new=57,manifest_files=197,original_bindings=20,frozen_bindings=13,receipt_exit_counts=record['receipt_exit_counts'],new_denials=False,review=ready)))
