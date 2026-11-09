"""Root documentary integration and target-only independent qualification packet."""
import os,resource
os.sched_setaffinity(0,sorted(os.sched_getaffinity(0))[:2])
resource.setrlimit(resource.RLIMIT_CPU,(120,120));resource.setrlimit(resource.RLIMIT_AS,(6*1024**3,6*1024**3))
from pathlib import Path
import json,hashlib,datetime,collections,re,shutil
from urllib.parse import urlsplit,unquote
P=Path(__file__).resolve().parent.parent;ROOT=P/'root-intake-r60';A=P/'expanded-corpus-r474';R=P/'qtransversal-directsum-source-review-sol-r1'
def sha(q):return hashlib.sha256(q.read_bytes()).hexdigest()
def dg(b):return hashlib.sha256(b).hexdigest()
def save(q,v):
 assert not q.exists(),str(q)
 q.write_text(json.dumps(v,indent=2)+'\n')
now=datetime.datetime.now(datetime.timezone.utc).isoformat();assert json.loads((P/'ledger.json').read_text())['accepted_new']==57
route=json.loads((ROOT/'selection-routing-r474.json').read_text());assert sha(A/'TASK.txt')==route['task_sha256'] and sha(A/'reservation.json')==route['reservation_sha256']
m=json.loads((A/'MANIFEST.json').read_text());entries={x['path']:x for x in m['files']};assert len(entries)==len(m['files'])==153
for n,v in entries.items():
 assert not Path(n).is_absolute() and '..' not in Path(n).parts
 q=A/n;assert not q.is_symlink() and sha(q)==v['sha256'] and q.stat().st_size==v['bytes'],n
exclusions=m['terminal_noncircular_self_exclusions'];assert set(exclusions)=={'MANIFEST.json','terminal_manifest.receipt.json','terminal_manifest.output.txt'}
assert {str(q.relative_to(A)) for q in A.rglob('*') if q.is_file()}==set(entries)|set(exclusions)
frozen=json.loads((A/'frozen-inputs.json').read_text());assert len(frozen)==13 and all(Path(n).parent==A and sha(Path(n))==h for n,h in frozen.items())
after=json.loads((A/'frozen-after.json').read_text());assert after['count']==13 and after['mismatches']==[]
prov=json.loads((A/'original-provenance.json').read_text());gates=json.loads((A/'results.json').read_text());ids=json.loads((A/'reservation.json').read_text())['ids'];assert len(ids)==len(prov)==20 and set(ids)==set(map(int,gates))=={x['id'] for x in prov}
chunks={};sources={};objects={}
for row in prov:
 q=Path(row['chunk']);assert q.is_relative_to(P.parent/'lanes/pi-mathdb-full-corpus-inventory-r301/corpus')
 if str(q) not in chunks:
  b=q.read_bytes();chunks[str(q)]=(dg(b),b.splitlines(keepends=True))
 h,lines=chunks[str(q)];assert h==row['chunk_sha256'];raw=lines[row['line']-1];obj=json.loads(raw);key=str(row['id']);objects[key]=obj;sources[key]=obj['source_url']
 assert obj['mathdb_id']==row['id'] and raw.endswith(b'\n') and row['newline'] is True and dg(raw)==row['raw_sha256'] and (A/'originals'/f'{key}.jsonl').read_bytes()==raw
 token=re.search(rb'"statement"\s*:\s*("(?:[^"\\]|\\.)*")',raw)[1]
 assert row['statement_key']=='statement' and token.decode()==row['token'] and dg(token)==row['token_sha256'] and json.loads(token)==obj['statement']==gates[key]['literal_statement'] and dg(obj['statement'].encode())==row['decoded_sha256']
receipts=[]
for q in sorted(A.glob('*.receipt.json')):
 v=json.loads(q.read_text());assert v['cwd']==str(A) and v['cpu_limit_s']==115 and v['as_limit_bytes']==6*1024**3 and v['deadline_s']==130
 receipts.append(dict(path=q.name,sha256=sha(q),exit=v['exit']))
assert json.loads((A/'terminal_manifest.receipt.json').read_text())['exit']==0
budget=json.loads((A/'search-budget.json').read_text());assert budget['calls_used']==3 and budget['queries_used']==9 and budget['maximum_calls']==3 and budget['maximum_queries']==9
charges=[json.loads(s) for s in (A/'search-charges.jsonl').read_text().splitlines()];assert len(charges)==3
prev=dict(calls_used=0,queries_used=0,maximum_calls=3,maximum_queries=9,charged_before_call=True)
for i,c in enumerate(charges,1):
 assert c['sequence']==i and c['before']==prev and sha(A/c['plan'])==c['plan_sha256'] and json.loads((A/c['plan']).read_text())['queries']==c['queries']
 nxt=dict(prev);nxt['calls_used']+=1;nxt['queries_used']+=len(c['queries']);assert c['after']==nxt;prev=nxt
 assert json.loads((A/f'search{i}-response.json').read_text())
assert prev==budget and sha(A/'charge_search.py')==sha(ROOT/'charge_search.py')
events=[json.loads(s) for s in (A/'guard-ledger.jsonl').read_text().splitlines()];counts=collections.Counter(e['event'] for e in events);assert counts==dict(attempt=9,success=8,unavailable=1)
for e in events:
 if e['event']=='success':assert sha(A/e['destination'])==e['sha256'] and (A/e['destination']).stat().st_size==e['bytes']
failed=next(e for e in events if e['event']=='unavailable');assert failed['status']==403 and failed['url']=='https://www2.math.upenn.edu/~pemantle/papers/negcor.pdf'
history=json.loads((A/'history-access.json').read_text());assert len(history)==782
forbidden=('formal','code-loop','code_loop','polynexus','crown','bunkbed','tournament','hat-bipartite')
assert all(not any(t in part.lower() for t in forbidden) for x in history for part in Path(x['path']).relative_to(P).parts)
assert all(not any(f'expanded-corpus-r{n}' in x['path'] for n in [395,463,466]) for x in history)
record=dict(utc=now,source_lane=str(A),manifest_sha256=sha(A/'MANIFEST.json'),verified_manifest_files=153,verified_original_bindings=sorted(ids),verified_frozen_bindings=13,source_url_by_id=sources,task_reservation_genesis_verified=True,runner_receipts=receipts,receipt_exit_counts=dict(collections.Counter(str(x['exit']) for x in receipts)),guard_events=dict(counts),search_budget=budget,search_counter_continuity='All three live before/after states, exact plans/query strings, immutable helper and full saved JSON-string responses verified.',
 root_disposition='ZERO_QUALIFIED_SURVIVORS_373611_ASSIGNED_INDEPENDENT_REVIEW',
 scientific_summary='373611author full ordinary arbitrary-presentation transversal q-matroid directsum proof retained, two rank-envelope derivations cover mixed subspaces/allfinitefields/emptycases. Complete actualSaaltink2025 rank-envelope bridge makes routine-adaptation a concrete significance question; source2026 explicit noncoordinate conjecture strongest contrary case. No independentPASS or scientific acceptance.378317complete actual pinnedSidorenkoTheorem1.1-to-height2gradedgraph negation bridge routine/public0, upstream trusted not audited.382541actualArmstrongHillarTheorem1.4/Section11 public nonuniqueness0, printed determinant attributed not independently certified.382537sourceindex endpoint correction0 despite full intended m>=2Gram proof.376916fiber-majorization/allcoefficient and377606arbitrary-nonnearlysymmetric trace necessity gaps remain unpaid.',
 all20_gates=gates,reading_limits='Six assigned IDs relevant original passages on five works; fourteen original bodies unread. Seven nonpinned works plus one pinned upstream theorem PDF acquired,no final-equivalence or visual figure audit claim.',
 process='782 saved history path names prefiltered/checked,no root following protected external files. Exact sourceURL matches only distinct0811.0949scopes,not transferred. OneHTTP403 preserved/no retry. Material truncated source passages recovered, native/transient/writer telemetry limitations retained,no universal proceduralPASS.',
 root_scope='Documentary verification and routing only,no root mathematical solving/programs/Lean/checkers.',credit=0,accepted_new=57,target_new=60,formal_dispatch=False,terminal_self_exclusions=exclusions)
save(P/'expanded-corpus-r474-parent-integration.json',record)
den=json.loads((ROOT/'inherited-denials-r477.json').read_text());den['utc']=now;url=failed['url']
den['blocked_keys']=sorted(set(den['blocked_keys'])|{urlsplit(url).hostname.lower()+unquote(urlsplit(url).path).rstrip('/')})
den['blocked_artifacts']=sorted(set(den['blocked_artifacts'])|{'negcor.pdf','towards a theory of negative dependence'})
den['records'].append(dict(url=url,reason=dict(status=403,artifact='Pemantle Towards a theory of negative dependence / negcor.pdf',restriction='ENTIRE identified work ALL NEW hosts,versions,arxiv,authors,caches,mirrors,DOI/API,body/metadata deliveries unavailable. No retry,alternate identity correction or indirect recovery. Distinct original Uniform random spanning trees math0404099 not itself requested or denied.'),evidence=dict(path=str(A/'guard-ledger.jsonl'),sha256=sha(A/'guard-ledger.jsonl'))))
delta='Completedr474 zero qualified survivors.373611author full arbitrary-presentation/allsubspace q-transversal directsum proof now assigned independent proof/source/significance review; actualSaaltink2025 rank-envelope-to-target bridge makes routine-adaptation objection concrete,source2026 explicit conjecture strongestcontrarycase,no selfcredit or formaldispatch.378317complete pinnedSidorenkoTheorem1.1 height2gradedgraph application public/routine0;382541actualArmstrongHillar public nonuniqueness0 determinant attributed;382537indexrangecorrection0 intendedGramproof notnewcredit.376916majorization and377606allwordtracegaps unpaid. NEW Pemantle Towards a theory of negative dependence negcor.pdf at www2.math.upenn.edu/~pemantle/papers/negcor.pdf HTTP403 ENTIRE identified work ALL NEW alternate hosts/versions/arxiv/authors/caches/mirrors/DOI/API/body/metadata UNAVAILABLE,no retry/indirectrecovery. Distinct original Uniform random spanning trees math0404099 not denied.153ownfiles20originalbindings13frozen782savedhistorypaths verified;9GET8PDFsuccess1HTTP403,3search9queries.57/60unchanged.'
den['root_r474_scope']=delta;denpath=ROOT/'inherited-denials-r478.json';save(denpath,den)
assert not R.exists();R.mkdir();(R/'inputs').mkdir();base=P/'expanded-corpus-r433'
for name in ['bootstrap.py','run.py','write_lane.py','verify_frozen.py','registry-roots.json','source_get_guard.py','model-policy-sol-only.json']:shutil.copyfile(base/name,R/name)
shutil.copyfile(ROOT/'charge_search.py',R/'charge_search.py');shutil.copyfile(denpath,R/'inherited-denials.json')
literal=objects['373611'];shutil.copyfile(A/'originals/373611.jsonl',R/'inputs/original373611.raw.jsonl');save(R/'inputs/literal373611.json',literal);save(R/'inputs/author-gates373611.json',gates['373611'])
for name in ['FULLCANDIDATE.md','DORMANT-SOL-FORMAL-PLAN.md','search3-response.json','get-qmatroid.json','get-saaltink.json']:shutil.copyfile(A/name,R/'inputs'/name)
for name in ['fulcher.pdf','fulcher.txt','saaltink.pdf','saaltink.txt']:shutil.copyfile(A/'sources'/name,R/'inputs'/name)
shutil.copyfile(ROOT/'accepted57-review-context.json',R/'inputs/accepted57-scopes.json');prior=P/'spherical-error-monotonicity-source-review-sol-r1/inputs/prior39-routing.json';assert sha(prior)=='6493e29137d286242b09d96f97dfe39a9ca5146a8d73bcfa8177e4705d6aaff3';shutil.copyfile(prior,R/'inputs/prior39-scopes.json')
save(R/'reservation.json',dict(ids=[373611],rows=[literal],purpose='Independent all-presentation q-transversal directsum proof,fidelity,prior/significance qualification,no formaltools or selfacceptance'));(R/'reservation.sha256').write_text(sha(R/'reservation.json')+'  reservation.json\n');save(R/'search-budget.json',dict(calls_used=0,queries_used=0,maximum_calls=2,maximum_queries=6,charged_before_call=True))
task=f'''GPT-6.1 Sol high effort/default speed ONLY. Personally independently review MathDB373611 full arbitrary-presentation transversal q-matroid directsum proof,actual source/prior and scientific significance. No children/provider fallback/mathematical programs/formaltools/selfcredit. Current57/60 beyond39 prior,96total. Root orchestrates; you do mathematics/source adjudication.

FIRST shell command EXACTLY:
timeout 20 python3 -I -B {R}/bootstrap.py
Read COMPLETE printed TASK/AGENTS. SECOND EXACTLY:
timeout 140 python3 -I -B {R}/verify_frozen.py before
No punctuation/chaining. Bootstrap/standalone before-after verifiers explicit cap exceptions. ALL other substantive local operations through immutable ABSOLUTE {R}/run.py UNIQUE_LABEL Python stdin; authored writes immutable ABSOLUTE {R}/write_lane.py. Never rerun bootstrap/edit frozen helpers,inputs,TASK,caps. Preserve real failures,repair diagnostics under newlabels. Actualprotected/frozen/access/guard/counter/cap violation STOP/quarantine,no resets. Ordinary documentary typos/render/serialization failures not automatically access breach.

Sole assigned373611. Protected active peers expanded-corpus-r475 and adaptive-lp-path-source-review-sol-r1; no read/stat/hash/list/glob/poll even metadata. NO historical allowlist. Read ONLY own frozen inputs,own products,explicit PDFskill. No authorlane/ROOT/campaign/history bodies or embedded path follow. All formal/code-loop/Polynexus/crown/bunkbed/tournament/Hat bodies AND flat integration basenames protected. r395/r463/r466 evidence quarantined,no reuse/refetch seeds. Trusted57+39scope snapshots only boundedfamilycontext,no oldcertificate audit. Allwrites soleownlane,no/tmp/shared/parent/git/install/publish/accounts/messages.

Read full exactoriginal/literal and actual cached Fulcher2603.13550v1 Definition2.7,Definition2.12,Theorem4.7 proof and Conjecture4.8 plus all standing finitefield/dimension/presentation assumptions. Literal contains malformed op-latex control sequence; retain exact bytes and establish intended operation from actual source,not claim correctioncredit. Exact padded combined family is (A_i directsum E2)_i concatenated (E1 directsum B_j)_j,not naive embedded concatenation. Verify actualsource defines that exact candidate for arbitrary presentations,not just existence of some presentation. Every subspace X including non-split mixed X must becovered.

INDEPENDENTLY prove or break FULLCANDIDATE: q-transversal independence 'EVERY basis admits an injective avoiding assignment' versus some-basis/partialtransversal/dimension conventions; actual Saaltink2503.12201v1 Section3.1 induced rank,Theorem15 full Hall proof,Cor16,Theorem18. Inspect source Definition14 typographical dimension-n phrase against actual theorem/proof and Fulcherdefinition; do not invent a convention repair. Exact rank envelope r_C(X)=min_Y<=X(f_C(Y)+dimX-dimY),f_C(Y)=number of entries not containingY; prove/supply source bridges from original independence,not assume the result to beproved. Interpret original source union and directsum ranks literally.
Audit FIRST route intersection-min formula incl emptyfamily,finite minima,opposite inequalities and exact pair-index expansion; quotientmap Y to (E1/A_I)directsum(E2/B_J),kernel Ycap(A_IdirectsumB_J),image rank versus sum of marginal ranks,attainment/Ychoice,mixedspaces. Audit SECOND route nested minimizers and codimension inequality,monotonicf,projectionrestrictions,all directions. Keep original finite-field hypothesis,arbitraryprimepower,char2,zero ambient dimensions/zeroX/empty indices/repeats/wholeambient entries/nonminimalpresentations/loops. No coordinate representation or hidden canonical quotient splitting. Author two proofs not independentPASS. Personally derive exact final ordinary statement and adversarial tests by reasoning,not code/sweeps.

PRIMARY/significance: actual2025Saaltink theorem machinery plus source directsum rank admits complete short bridge. This is a concrete routine-adaptation objection,not automatically an exclusion. Strongest positive case: actualMarch2026 source explicitly states arbitrary noncoordinate Conj4.8 after coordinateTheorem4.7; proof removes that exact restriction. Strongest contrary case: general established rank/union construction already pays whole target by complete application,with little new content. Pay exact primary-to-target bridge and compare actual hypotheses/objects,then RECOMMEND significance disposition root alone decides. Do not infer novelty from authors calling it a conjecture,shortness from standardtools,or routine status from familiar jargon. No earlier printed exact proof claim unless actualprimarybody authenticated. Ordinarycorrectness,existing theorem reduction,significance,priority and sourcefidelity separate gates.

Bounded current/final/corrections and targeted concrete prior/public-counterpart comparison. Own copied search3response is navigation,notproof. Concrete trureturing.org/research/saaltink-2025-q-transversal-representability/ claim 'Every q-transversal matroid is representable over a finite extension' is a distinct claim,not a paid directsum theorem or current registry clearance. If relevant read actualbody and authenticate chronology/author/proof and complete representation-to-directsum bridge; otherwise report boundednonmatch,not specificmatchingunreadproofHOLD by title alone. Four exactregistry-rootmetadata artifacts unavailable,no refresh/reconstruction. No worldwide novelty from boundednonmatches; genericworldwideunknown not automaticveto. Specifically applicable unread matching theorem preciseHOLD. Sourcev1 not final/currentversion equivalence without actual bounded evidence. Compare full trusted57+39scopes; sameqmatroid/coding vocabulary not familyidentity; all empty/mixed/coordinate/parameter variants onefamily,helpers/formalizationnotcredit.

Materialsource equation/conjecture pages visually inspect using PDFskill /home/mj-kang/.codex/plugins/cache/openai-primary-runtime/pdf/26.1103.10131/skills/pdf/SKILL.md (announce/read). NoPDFauthoring requested. Actualread/proof/visual limits candid; copied PDFs alreadyacquired,no need refetch merelytoobservecachedbody.

NO mathprograms/enumeration/numericaltests/experiments/CAS/solvers/Lean/compiler/checker/formalAPI. Personal ordinarymath only;documentary/hash/PDFprocessing permitted. Conditional dormant Solformal plan ONLY if fullordinaryliteral/scientific gates survive,exact sourceobjects/independence/rankbridges/universal endpoint/fullallowedaxioms listed. No implementation,dispatch,selfacceptance. If routineexclusion recommended,no costly formalpipeline;preservecompleteproof and contrarycase.

Network: BEFOREeachrequest read ENTIRE inheriteddenials/recovermaterialtruncation. SoleGET immutable source_get_guard.py UNDERrun.py,ONE manuallyselected exact persisted plan/invocation,url/routes/destination/source_identity/purpose,route['373611'],newown sources destination,identity/purpose>=12chars. Max8GETHOPS whole review,redirects charged. Max2nativeSEARCHcalls6exactquerystrings total. No customHTTP/curl/wget/requests/HEAD/nativeopenfetch/browser/API/accounts/POST/TLS/cookie/JS/metarefresh workarounds. Everyfailure identifiedworkALLNEWhosts/versions/arxiv/authors/caches/mirrors/DOI/API/body/metadata unavailable,no retry/identitycorrection/indirectrecovery. Transport200nonpaper separate scientificclassification,guardhistory append-only unchanged. NewPemantle Towards a theory of negative dependence negcor.pdf403 entirework unavailable,distinct Uniform random spanning trees math0404099 notdenied; Barmakthmafinal404/LR0904.4778finalredirect/virusfinals/allolderblocks binding. No alternate recovery/searchforcopies.
BeforeEACHnativeSEARCH persist exactquerieslistplan viawriter,read LIVEcounter/chargeledger,precharge immutable ABSOLUTEcharge_search.py underrunner. No manual counters/reset/refund. Save FULLactualresponseIMMEDIATELY beforeotherwork,plainJSON/stringserialization,no btoa/TextEncoder. Preserve serializationfailures,recover SAME in-memoryresponse,noextra networkcall. Searchsnippets/navigationnotprimaryproof. No newroots/repoHEAD/README/APIbranch reconstruction of fourdeniedmetadata artifacts.

Capsaffinity<=2,childCPU115/supervisor120,AS6GiB,sampledgroupRSS6GiB,deadline130/outer140,arena2. True synchronousrunnerreceipts,outputs,resources,reaping,no backgroundjobs. StandaloneverifierCPU120exception notnestedchild115. Native/transient/writer/supervisorpeaks unknown,no universalcomplianceclaim.

Deliver REVIEW.md,independent full PROOF.md orprecise GAP.md,keyedreview.json373611 separate literal/source/ordinary/prior/novelty/significance/family/formal/independent/procedure/acceptance gates,exactprimarybridge/strongestcontraryobjections,source/read/figure/access/search/resourceinventories,actualreceipts/hashmanifest. Final standalone frozen-after,thenmanifest EVERYownfile/helpers/frozeninputs/reports/plans/payloads/responses/guard/searchledgers and EVERYcompletedreceiptJSON,preciselynamed terminalnoncircular exclusions,no frozenwritesafter. Complete boundedreview,notacknowledgment/acquisition-only handback. Credit0,57/60unchanged untilrootacceptance.
'''
(R/'TASK.txt').write_text(task);files=[q for q in R.iterdir() if q.is_file() and q.name!='search-budget.json']+list((R/'inputs').iterdir());save(R/'frozen-inputs.json',{str(q):sha(q) for q in files})
ready=dict(utc=now,lane=str(R),mathdb_id=373611,task_sha256=sha(R/'TASK.txt'),frozen_bindings=len(files),model='gpt-6.1-sol',reasoning='high',service='default',accepted_new=57,credit=0,protected_peers=['expanded-corpus-r475','adaptive-lp-path-source-review-sol-r1'],source_copy_scope='Cleanr474 target-only exactliteral,authorproof,dormantplan,actualFulcher/Saaltinkbodies,datednavigation,57+39scopes,no quarantine evidence')
save(ROOT/'qtransversal-review-r1-ready.json',ready);save(ROOT/'selection-routing-qtransversal-review-r1.json',dict(ids=[373611],sources=[literal['source_url'],'https://arxiv.org/abs/2503.12201'],lane=str(R),task_sha256=ready['task_sha256'],metadata_only=True));save(ROOT/'r474-pemantle-boundary-delta.json',dict(utc=now,message=delta,immutable_worker_inputs_unchanged=True,new_protected_peer=R.name))
print(json.dumps(dict(manifest_files=153,original_bindings=20,frozen_bindings=13,receipt_exit_counts=record['receipt_exit_counts'],review=ready,accepted_new=57)))
