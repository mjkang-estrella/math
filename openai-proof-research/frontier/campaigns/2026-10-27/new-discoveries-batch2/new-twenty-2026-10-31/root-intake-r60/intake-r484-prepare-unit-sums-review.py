"""Root documentary integrity and target-only independent review preparation."""
import os,resource
os.sched_setaffinity(0,sorted(os.sched_getaffinity(0))[:2]);resource.setrlimit(resource.RLIMIT_CPU,(120,120));resource.setrlimit(resource.RLIMIT_AS,(6*1024**3,6*1024**3))
from pathlib import Path
import json,hashlib,datetime,collections,re,shutil
P=Path(__file__).resolve().parent.parent;ROOT=P/'root-intake-r60';A=P/'expanded-corpus-r484';R=P/'cyclic-unit-fixed-sums-source-review-sol-r1'
def sha(q):return hashlib.sha256(q.read_bytes()).hexdigest()
def dg(b):return hashlib.sha256(b).hexdigest()
def save(q,v):
 assert not q.exists(),str(q)
 q.write_text(json.dumps(v,indent=2)+'\n')
now=datetime.datetime.now(datetime.timezone.utc).isoformat();assert json.loads((P/'ledger.json').read_text())['accepted_new']==57
route=json.loads((ROOT/'selection-routing-r484.json').read_text());assert sha(A/'TASK.txt')==route['task_sha256'] and sha(A/'reservation.json')==route['reservation_sha256']
m=json.loads((A/'MANIFEST.json').read_text());entries=m['files'];assert len(entries)==140
for n,v in entries.items():
 assert not Path(n).is_absolute() and '..' not in Path(n).parts
 q=A/n;assert not q.is_symlink() and sha(q)==v['sha256'] and q.stat().st_size==v['bytes'],n
exclusions=m['terminal_noncircular_self_exclusions'];assert set(exclusions)=={'MANIFEST.json','manifest_finish.receipt.json','manifest_finish.output.txt'}
assert {str(q.relative_to(A)) for q in A.rglob('*') if q.is_file()}==set(entries)|set(exclusions)
frozen=json.loads((A/'frozen-inputs.json').read_text());assert len(frozen)==13 and all(Path(n).parent==A and sha(Path(n))==h for n,h in frozen.items())
after=json.loads((A/'frozen-after.json').read_text());assert after['count']==13 and after['mismatches']==[]
prov=json.loads((A/'provenance.json').read_text());gates=json.loads((A/'results.json').read_text());records=json.loads((A/'records.json').read_text());ids=json.loads((A/'reservation.json').read_text())['ids'];assert len(ids)==len(prov)==20 and set(ids)==set(map(int,gates))==set(map(int,records))=={v['id'] for v in prov}
chunks={};sources={}
for row in prov:
 q=Path(row['chunk']);assert q.is_relative_to(P.parent/'lanes/pi-mathdb-full-corpus-inventory-r301/corpus')
 if str(q) not in chunks:
  b=q.read_bytes();chunks[str(q)]=(dg(b),b.splitlines(keepends=True))
 h,lines=chunks[str(q)];assert h==row['chunk_sha256'];raw=lines[row['line']-1];obj=json.loads(raw);key=str(row['id'])
 assert row['newline'] is True and raw.endswith(b'\n') and dg(raw)==row['raw_sha256'] and obj==records[key] and obj['mathdb_id']==row['id'] and (A/'originals'/f'{key}.jsonl').read_bytes()==raw
 token=re.search(rb'"statement"\s*:\s*("(?:[^"\\]|\\.)*")',raw)[1]
 assert token.decode()==row['raw_statement_token'] and dg(token)==row['raw_statement_token_sha256'] and json.loads(token)==obj['statement']==gates[key]['literal'] and dg(obj['statement'].encode())==row['statement_sha256'];sources[key]=obj['source_url']
receipts=[]
for q in sorted(A.glob('*.receipt.json')):
 v=json.loads(q.read_text());assert v['cwd']==str(A) and v['cpu_limit_s']==115 and v['as_limit_bytes']==6*1024**3 and v['deadline_s']==130
 receipts.append(dict(path=q.name,sha256=sha(q),exit=v['exit']))
assert json.loads((A/'manifest_finish.receipt.json').read_text())['exit']==0
budget=json.loads((A/'search-budget.json').read_text());assert budget==dict(calls_used=3,queries_used=9,maximum_calls=3,maximum_queries=9,charged_before_call=True)
charges=[json.loads(s) for s in (A/'search-charges.jsonl').read_text().splitlines()];assert len(charges)==3
prev=dict(calls_used=0,queries_used=0,maximum_calls=3,maximum_queries=9,charged_before_call=True)
for i,c in enumerate(charges,1):
 assert c['sequence']==i and c['before']==prev and sha(A/c['plan'])==c['plan_sha256'] and json.loads((A/c['plan']).read_text())['queries']==c['queries']
 nxt=dict(prev);nxt['calls_used']+=1;nxt['queries_used']+=len(c['queries']);assert c['after']==nxt;prev=nxt
 assert json.loads((A/f'search{i}-response.json').read_text())
assert prev==budget and sha(A/'charge_search.py')==sha(ROOT/'charge_search.py')
events=[json.loads(s) for s in (A/'guard-ledger.jsonl').read_text().splitlines()];counts=collections.Counter(e['event'] for e in events);assert counts==dict(attempt=6,success=6)
for e in events:
 if e['event']=='success':assert sha(A/e['destination'])==e['sha256'] and (A/e['destination']).stat().st_size==e['bytes']
history=json.loads((A/'history-access.json').read_text());assert len(history)==802;forbidden=('formal','code-loop','code_loop','polynexus','crown','bunkbed','tournament','hat-bipartite')
assert all(not any(t in part.lower() for t in forbidden) for x in history for part in Path(x['path']).relative_to(P).parts)
assert all(not any(f'expanded-corpus-r{n}' in x['path'] for n in [395,463,466,482]) for x in history)
summary='316244authorn16/eightunits/k4paritynegationretained,targetactualsource0704.0541v1Conj1.2visuallycheckedbyauthor;source/domaincorrectionversussignificantoutcomeandtargetedprior/independentreviewunpaid,assignedreview.381028exactalternatingpolynomial/dividedsymmetrizationreductionpaid,allnevaluation/cancellationbijectionunpaid.316628arbitrarycentrallysymmetricfacefree-sumconstructionunpaid;sourceexponent3/cube/crosspolytopecasespublic,evenparitysliceinvalidatesnaiveoddprimeconversion.316626actualBaumeisterLadischALCO2018TheoremApublicsolutionincludingpermutationC6exceptionbridge0;316627actualFrieseLadisch1411.0899v3publiccounterexampleandpermutationrepresentationLemma9.10bridge0,internalcharactercriterion/Fig5notindependentlyaudited.316629sourceifversusiffscopeunqualified.'
record=dict(utc=now,source_lane=str(A),task_reservation_genesis_verified=True,manifest_sha256=sha(A/'MANIFEST.json'),verified_manifest_files=140,verified_original_bindings=sorted(ids),verified_frozen_bindings=13,source_url_by_id=sources,all20_gates=gates,runner_receipts=receipts,receipt_exit_counts=dict(collections.Counter(str(x['exit']) for x in receipts)),guard_events=dict(counts),search_budget=budget,root_disposition='ZERO_QUALIFIED_SURVIVORS_316244_ASSIGNED_SCOPE_PROOF_SIGNIFICANCE_REVIEW',scientific_summary=summary,reading_limits='SixIDsactualoriginal/finaltargetpassages,fourteenoriginalsunread;fivePDFsplusarxivmetadata,nofullinternalrepresentationorallfinalaudit.',process='802savedhistorypathnameschecked,norootprotectedexternalpathfollow.6GETsuccess0denial3search9queries,butnotargeted316244priorsearchbeforeobstructionidentified. Missingfitzrenderfailedexit1retained,Popplerrecoverypassed,noinstall/unchangedrerun. Materialsourcepassagesandglyphrecovered;actualsamples/nativetransientwriterlimitsretained,nouniversalcomplianceclaim.',root_scope='Documentaryverification/routingonly,norootmathematics/programs/Lean/checkers.',credit=0,accepted_new=57,target_new=60,formal_dispatch=False,terminal_self_exclusions=exclusions)
save(P/'expanded-corpus-r484-parent-integration.json',record)
den=json.loads((ROOT/'inherited-denials-r488.json').read_text());den['utc']=now
delta='Completedr484zeroqualifiedsurvivors. '+summary+'140ownfiles20bindings13frozen802savedhistorypathsverified,6GETsuccess3search9queries,nonewdenials. Missingfitzrendernonpassretained/Popplerrecovered.57/60unchanged.'
den['root_r484_scope']=delta;denpath=ROOT/'inherited-denials-r489.json';save(denpath,den)
assert not R.exists();R.mkdir();(R/'inputs').mkdir();base=P/'expanded-corpus-r433'
for name in ['bootstrap.py','run.py','write_lane.py','verify_frozen.py','registry-roots.json','source_get_guard.py','model-policy-sol-only.json']:shutil.copyfile(base/name,R/name)
shutil.copyfile(ROOT/'charge_search.py',R/'charge_search.py');shutil.copyfile(denpath,R/'inherited-denials.json')
literal=records['316244'];shutil.copyfile(A/'originals/316244.jsonl',R/'inputs/original316244.raw.jsonl');save(R/'inputs/literal316244.json',literal);save(R/'inputs/author-gates316244.json',gates['316244'])
for name in ['FULLCANDIDATE.md','DORMANT-SOL-FORMAL-PLAN.md','get-sums-plan.json','get-sums-meta-plan.json']:shutil.copyfile(A/name,R/'inputs'/name)
for name in ['complete-sums.pdf','complete-sums.txt','complete-sums-abs.html']:shutil.copyfile(A/'sources'/name,R/'inputs'/name)
shutil.copyfile(ROOT/'accepted57-review-context.json',R/'inputs/accepted57-scopes.json');prior=P/'spherical-error-monotonicity-source-review-sol-r1/inputs/prior39-routing.json';assert sha(prior)=='6493e29137d286242b09d96f97dfe39a9ca5146a8d73bcfa8177e4705d6aaff3';shutil.copyfile(prior,R/'inputs/prior39-scopes.json')
save(R/'reservation.json',dict(ids=[316244],rows=[literal],purpose='Independentparitycounterexample/sourcequantifiers/priorandsignificancereview,noformaltools/selfacceptance'));(R/'reservation.sha256').write_text(sha(R/'reservation.json')+'  reservation.json\n');save(R/'search-budget.json',dict(calls_used=0,queries_used=0,maximum_calls=2,maximum_queries=6,charged_before_call=True))
task=f'''Use ONLY GPT-6.1 Sol, high effort, default speed. Personally review MathDB316244's proposed n=16 fixed-length unit-sum refutation. Prioritize exact source scope/notation and scientific significance, then independent ordinary proof and bounded priors. No children, fallback, mathematical programs, formal tools or self-credit. Current57/60 beyond39 prior,96total. Root orchestrates; you do mathematics.

FIRST shell command EXACTLY:
timeout 20 python3 -I -B {R}/bootstrap.py
Read COMPLETE printed TASK/AGENTS. SECOND EXACTLY:
timeout 140 python3 -I -B {R}/verify_frozen.py before
No punctuation/chaining. Bootstrap/standalone verifiers explicit cap exceptions. Every other substantive local operation uses immutable ABSOLUTE {R}/run.py UNIQUE_LABEL Python stdin; authored writes immutable ABSOLUTE {R}/write_lane.py. Never rerun bootstrap/edit frozen helpers,inputs,TASK,caps. Preserve failures and targeted repairs under fresh labels. Actual protected/frozen/access/guard/counter/cap breach STOP/quarantine/no reset. Ordinary documentary typo/render/serialization failures not automatically policy breaches.

Sole316244. Protected active/planned peers eps-zero-weight-source-review-sol-r1 and poset-polyantimatroid-staircase-source-review-sol-r1; no read/stat/hash/list/glob/poll even metadata. NO history allowlist. Own frozen inputs/products and explicit PDF skill only; no author lane/ROOT/campaign/history/embedded paths. All formal/code-loop/Polynexus/crown/bunkbed/tournament/Hat bodies AND flat integration basenames protected. ALL r395/r463/r466/r482 outputs/acquisitions/claims quarantined,no reuse/refetch seeds. Public repository /server/api/.../content is forbidden API despite guard transport200; inspect planned URL before request. Trusted57+39 scope snapshots only bounded context,no certificate audit. All writes sole own lane,no/tmp/shared/parent/git/install/publish/accounts/messages.

Read exact original/literal and actual cached Hamidoune-Llado-Serra0704.0541v1 COMPLETE definitions/introduction/standing assumptions,main theorem/proof,Conjecture1.2,restricted-sum notation,coprimality,prime/composite/odd hypotheses,all length/ceiling/square-root quantifiers. Author says source visually prints arbitrary n and EXACT k distinct summands. Independently check this claim,including whether a global assumption,nearby convention,union over lengths,or notation meaning was missed. Do not treat the author's visual report as your fidelity PASS. Distinguish fixed-length k wedge A from arbitrary subset sums or at-most-k sums. If source differs, provide precise source/corpus correction with zero credit,not a new theorem obtained by changing notation.

Visually inspect relevant source definition,Conjecture1.2 and glyphs using PDFskill /home/mj-kang/.codex/plugins/cache/openai-primary-runtime/pdf/26.1103.10131/skills/pdf/SKILL.md (announce/read). No PDF authoring. Actual current/final/correction comparison within bounded access may clarify whether even modulus was an omitted domain restriction. Cached arxiv metadata only listsv1/nojournalreference; that does not establish no final/correction.

If fixed-length/all-n reading is faithful, INDEPENDENTLY verify n16,A={{2j+1 mod16:0<=j<8}},all8distinct/coprime16,|A|>=sqrt60,k=ceil(sqrt15)=4,and every allowed four-distinct sum in the eight even residues. Pay strict/non-strict subset conventions,nonempty family,modular quotient/cardinality,positive n/k,ranges. An ordinary parity argument is enough,no exhaustive list/program required. Check author infinite-powers-of-two extension if used,onefamily not extra outcomes. No statement about an intended corrected odd-modulus theorem unless proved.

Scientific gate is central. Strongest positive case: a genuine full printed conjecture negation at a substantial nonempty unit set. Strongest contrary case: the entire mechanism is an even-modulus parity/domain defect in extending a prime theorem,so result is a source/domain correction expressly excluded from campaign discovery credit. Root alone adjudicates; recommend a candid classification. Do not infer significance from exact source conjecture wording,or reject just because proof is short/standard. If claiming routine-prior exclusion, authenticate an actual complete applicable primary-to-target bridge; if domain correction is the reason, say that directly and distinguish it from a prior-result claim. No unsupported earlier-exact-printed-refutation assertion.

Bounded targeted prior/current/final comparison: no targeted316244 prior search was done by author because budget exhausted on other routes. Read actual primary definitions/theorem/proof for any concrete matching claim,not snippets. Do not transfer Olson's prime result to the composite fixed-length target by name. A specific matching unread body is precise HOLD; generic worldwide unknown is not automatic veto, bounded nonmatches not novelty. Four registry-root metadata artifacts unavailable,no refresh/reconstruction via README/tree/API/branch/version. Distinct primary papers not blanket denied. Compare supplied57+39 full scopes only; other finite-group/ring/parity results are not automatically same family,but all even-modulus/unit/length variants onefamily. Domain/source/endpoint corrections,helpers,formalization,parameter variants and public/routine outcomes earn zero.

No mathematical programs/enumeration/numerical tests/experiments/CAS/solver/Lean/compiler/checker/formalAPI. Personal ordinary reasoning only,documentary/hash/source/PDF processing allowed. No costly formal plan if domain/routine/public exclusion or fidelity GAP. A conditional dormant Sol plan only if full literal ordinary and scientific gates survive,with exact cyclic-group units/restrictedsum/ceil/cardinality/universalnegation bridges and permitted axioms. No implementation,dispatch,selfacceptance.

Network: read ENTIRE inherited-denials/recover material truncations before requests. Sole GET immutable source_get_guard.py UNDERrun.py. ONE manually selected exact persisted plan/invocation,url/routes/destination/source_identity/purpose,route['316244'],new own sources destination,identity/purpose>=12chars. Max6 GET HOPS total,redirects charged. Max2 native SEARCH calls6 exactquerystrings total. No API including public repository/server/api bitstreams,customHTTP/curl/wget/requests/HEAD/nativeopenfetch/browser/accounts/POST/TLS/cookie/JS/meta-refresh workaround. Every failure identifiedwork ALL NEW hosts/versions/arxiv/authors/caches/mirrors/DOI/API/body/metadata unavailable;no retry/identity correction/indirect recovery. Guard history unchanged; transport200nonpaper classification separate. Inherited staircase0806.2096 final DOI blockedHTTP,all older work blocks and four registry roots binding; no HTTPS upgrade or indirect recovery. No actual prohibited HTTP fetch was performed by r483; guard reporting error is preserved,not permission to repair it.
Before EACH native SEARCH persist exactqueries-listplan via writer,read LIVE counter/ledger,precharge immutable ABSOLUTEcharge_search.py under runner. Never manually reset/refund/edit counters/ledger. Save FULL actual response immediately before other work,plainJSON/string serialization; no btoa/TextEncoder. Preserve failures,recover SAME in-memoryresponse without extra call. Search excerpts navigation,not proof.

Caps affinity<=2,childCPU115/supervisor120,AS6GiB,sampledgroupRSS6GiB,deadline130/outer140,arena2. Actual synchronous runner receipts/output/resources/reaping;no backgroundjobs. Standalone verifierCPU120 exception not nestedunderchild115. Native/transient/writer/supervisor peaks unknown,no universalcomplianceclaim.

Deliver REVIEW.md,independent PROOF.md or precise GAP.md,keyedreview.json316244 separate literal/source/ordinary/prior/novelty/significance/family/formal/independent/procedure/acceptance gates,source map,strongest opposing cases,inventories for read/visual/access/search/resources,actual receipts/hashmanifest. Final standalone frozen-after then manifest EVERY own file/helpers/frozeninputs/reports/plans/payloads/responses/ledgers/EVERY completed receiptJSON,precisely named terminalnoncircular exclusions,no later frozenwrites. Complete bounded review,not acknowledgment/acquisition-only. Credit0,57/60 unchanged until root acceptance.
'''
(R/'TASK.txt').write_text(task);files=[q for q in R.iterdir() if q.is_file() and q.name!='search-budget.json']+list((R/'inputs').iterdir());save(R/'frozen-inputs.json',{str(q):sha(q) for q in files})
ready=dict(utc=now,lane=str(R),mathdb_id=316244,task_sha256=sha(R/'TASK.txt'),frozen_bindings=len(files),model='gpt-6.1-sol',reasoning='high',service='default',accepted_new=57,credit=0,protected_peers=['eps-zero-weight-source-review-sol-r1','poset-polyantimatroid-staircase-source-review-sol-r1'],source_copy_scope='Cleanr484targetonlyliteral/authorproof/cachedactualsumsbody/metadata/dormantplan/57+39scopes,noquarantine')
save(ROOT/'unit-sums-review-r1-ready.json',ready);save(ROOT/'selection-routing-unit-sums-review-r1.json',dict(ids=[316244],sources=[literal['source_url']],lane=str(R),task_sha256=ready['task_sha256'],metadata_only=True));save(ROOT/'r484-completion-boundary-delta.json',dict(utc=now,message=delta,new_protected_peer=R.name,immutable_worker_inputs_unchanged=True))
print(json.dumps(dict(manifest_files=140,frozen_bindings=13,original_bindings=20,receipt_exit_counts=record['receipt_exit_counts'],review=ready)))
