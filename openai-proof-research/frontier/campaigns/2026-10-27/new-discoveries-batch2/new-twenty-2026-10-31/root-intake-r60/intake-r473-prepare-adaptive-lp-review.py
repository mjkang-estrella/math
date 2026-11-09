"""Root documentary intake and clean, target-only independent review preparation."""
import os,resource
os.sched_setaffinity(0,sorted(os.sched_getaffinity(0))[:2])
resource.setrlimit(resource.RLIMIT_CPU,(120,120));resource.setrlimit(resource.RLIMIT_AS,(6*1024**3,6*1024**3))
from pathlib import Path
import json,hashlib,datetime,collections,re,shutil
from urllib.parse import urlsplit,unquote
P=Path(__file__).resolve().parent.parent;ROOT=P/'root-intake-r60';A=P/'expanded-corpus-r473';R=P/'adaptive-lp-path-source-review-sol-r1'
def sha(q):return hashlib.sha256(q.read_bytes()).hexdigest()
def dg(b):return hashlib.sha256(b).hexdigest()
def save(q,v):
 assert not q.exists(),str(q)
 q.write_text(json.dumps(v,indent=2)+'\n')
now=datetime.datetime.now(datetime.timezone.utc).isoformat();assert json.loads((P/'ledger.json').read_text())['accepted_new']==57
route=json.loads((ROOT/'selection-routing-r473.json').read_text());assert sha(A/'TASK.txt')==route['task_sha256'] and sha(A/'reservation.json')==route['reservation_sha256']
manifest=json.loads((A/'manifest.json').read_text());entries=manifest['files'];assert len(entries)==114
for n,h in entries.items():
 assert not Path(n).is_absolute() and '..' not in Path(n).parts
 q=A/n;assert not q.is_symlink() and sha(q)==h,n
exclusions=manifest['terminal_non_circular_self_exclusions'];assert set(exclusions)=={'manifest.json','manifest_finalize.receipt.json','manifest_finalize.output.txt'}
assert {str(q.relative_to(A)) for q in A.rglob('*') if q.is_file()}==set(entries)|set(exclusions)
frozen=json.loads((A/'frozen-inputs.json').read_text());assert len(frozen)==13 and all(Path(n).parent==A and sha(Path(n))==h for n,h in frozen.items())
after=json.loads((A/'frozen-after.json').read_text());assert after['count']==13 and after['mismatches']==[]
originals=json.loads((A/'originals.json').read_text());gates=json.loads((A/'results.json').read_text());ids=json.loads((A/'reservation.json').read_text())['ids'];assert len(ids)==len(originals)==20 and set(ids)==set(map(int,gates))=={x['object']['mathdb_id'] for x in originals}
chunks={};sources={}
for row in originals:
 q=Path(row['chunk']);assert q.is_relative_to(P.parent/'lanes/pi-mathdb-full-corpus-inventory-r301/corpus')
 if str(q) not in chunks:
  b=q.read_bytes();chunks[str(q)]=(dg(b),b.splitlines(keepends=True))
 h,lines=chunks[str(q)];assert h==row['chunk_sha256'];raw=lines[row['line']-1];obj=json.loads(raw)
 assert raw.endswith(b'\n') and row['newline'] is True and row['raw'].encode()==raw and dg(raw)==row['raw_sha256'] and row['object']==obj
 key=str(obj['mathdb_id']);assert (A/'raw'/f'{key}.jsonl').read_bytes()==raw and gates[key]['literal']==obj['statement'];sources[key]=obj['source_url']
 token=re.search(rb'"statement"\s*:\s*("(?:[^"\\]|\\.)*")',raw)[1]
 assert token.decode()==row['raw_statement_token'] and dg(token)==row['raw_statement_token_sha256'] and json.loads(token)==obj['statement'] and dg(obj['statement'].encode())==row['decoded_statement_sha256']
receipts=[]
for q in sorted(A.glob('*.receipt.json')):
 v=json.loads(q.read_text());assert v['cwd']==str(A) and v['cpu_limit_s']==115 and v['as_limit_bytes']==6*1024**3 and v['deadline_s']==130
 receipts.append(dict(path=q.name,sha256=sha(q),exit=v['exit']))
assert json.loads((A/'manifest_finalize.receipt.json').read_text())['exit']==0
budget=json.loads((A/'search-budget.json').read_text());assert budget['calls_used']==3 and budget['queries_used']==9 and budget['maximum_calls']==3 and budget['maximum_queries']==9
charges=[json.loads(s) for s in (A/'search-charges.jsonl').read_text().splitlines()];assert len(charges)==3
prev=dict(calls_used=0,queries_used=0,maximum_calls=3,maximum_queries=9,charged_before_call=True)
for i,c in enumerate(charges,1):
 assert c['sequence']==i and c['before']==prev and sha(A/c['plan'])==c['plan_sha256'] and json.loads((A/c['plan']).read_text())['queries']==c['queries']
 nxt=dict(prev);nxt['calls_used']+=1;nxt['queries_used']+=len(c['queries']);assert c['after']==nxt;prev=nxt
 assert (A/f'search{i}-response.txt').read_text().strip()
assert prev==budget and sha(A/'charge_search.py')==sha(ROOT/'charge_search.py')
events=[json.loads(s) for s in (A/'guard-ledger.jsonl').read_text().splitlines()];counts=collections.Counter(e['event'] for e in events);assert counts==dict(attempt=6,success=5,unavailable=1)
for e in events:
 if e['event']=='success':assert sha(A/e['destination'])==e['sha256'] and (A/e['destination']).stat().st_size==e['bytes']
failed=next(e for e in events if e['event']=='unavailable');assert failed['status']==404 and failed['url']=='https://people.kth.se/~jbarmak/thmafinal.pdf'
history=json.loads((A/'history-access.json').read_text());assert len(history['access'])==779
forbidden=('formal','code-loop','code_loop','polynexus','crown','bunkbed','tournament','hat-bipartite')
assert all(not any(t in part.lower() for t in forbidden) for x in history['access'] for part in Path(x['path']).relative_to(P).parts)
assert all(not any(f'expanded-corpus-r{n}' in x['path'] for n in [395,463,466]) for x in history['access'])
record=dict(utc=now,source_lane=str(A),manifest_sha256=sha(A/'manifest.json'),verified_manifest_files=114,verified_original_bindings=sorted(ids),verified_frozen_bindings=13,source_url_by_id=sources,task_reservation_genesis_verified=True,runner_receipts=receipts,receipt_exit_counts=dict(collections.Counter(str(x['exit']) for x in receipts)),guard_events=dict(counts),search_budget=budget,
 search_counter_continuity='All three live states, exact plan digests/query strings, immutable helper and full text responses preserved. Native response byte-completeness is supported by author inventories, not independent root network replay.',
 root_disposition='ZERO_QUALIFIED_SURVIVORS_376636_ASSIGNED_INDEPENDENT_SCOPE_PROOF_REVIEW',
 scientific_summary='316630actualHaase1503.04002 exact public face/orbit-stabilizer theorem0;316557actualArdilaPostnikov1211.1368Prop2 exact public HoltzRon refutation0 with real deletion-space reconstruction.382558cone-intersection nerve construction lacks simple-homotopy bridge; specifically applicable Barmak primary404 remains unread.376636actualone-sided-bound/all-violated-cut path propagation plus fixed-L independent-block amplification author argument retained, no full-literal acceptance because random-ensemble/quantifiers/source-final/significance remain unpaid. Proposed configuration-model moment argument incomplete, not certified. All path/rate/block/algorithm variants one family.',
 all20_gates=gates,reading_limits='Three assigned originals read in relevant passages,seventeen originals unread,two later public solutions additionally read,no figure visual audit or exhaustive final/correction clearance.',
 process='Wrong initial literal key produced empty temporary extraction; corrected under fresh label, retained receipt. One actual404 failure preserved with no retry. Material truncations recovered; native/transient/writer telemetry limitations retained.779 own saved historical path names checked,no root follow of external protected paths. LatestLR denial steering applied without retrieval or further history access.',
 root_intake_reader_repair='Read-only schema probe initially assumed manifest files list, stopped on dict slicing KeyError before any mutations. Recovered actual dict schema; worker evidence unchanged.',
 root_scope='Documentary provenance/integrity and routing only,no root mathematical solving/programs/Lean/checkers.',credit=0,accepted_new=57,target_new=60,formal_dispatch=False,terminal_self_exclusions=exclusions)
save(P/'expanded-corpus-r473-parent-integration.json',record)
den=json.loads((ROOT/'inherited-denials-r476.json').read_text());den['utc']=now
url=failed['url'];den['blocked_keys']=sorted(set(den['blocked_keys'])|{urlsplit(url).hostname.lower()+unquote(urlsplit(url).path).rstrip('/')})
den['blocked_artifacts']=sorted(set(den['blocked_artifacts'])|{'thmafinal.pdf',"on quillen's theorem a for posets"})
den['records'].append(dict(url=url,reason=dict(status=404,artifact="Barmak On Quillen's theorem A for posets",restriction='ENTIRE identified Barmak work ALL NEW alternate hosts,versions,arxiv,authors,caches,mirrors,DOI/API,body/metadata deliveries unavailable. No retry,identity correction or indirect recovery. Distinct original Kozlov math0503613 is not denied by this different-work failure.'),evidence=dict(path=str(A/'guard-ledger.jsonl'),sha256=sha(A/'guard-ledger.jsonl'))))
delta='Completedr473 zero qualified survivors.316630actualHaase1503.04002 exact public theorem0;316557actualArdilaPostnikov1211.1368Prop2 public refutation0.376636author all-violated-cut path propagation/fixed-block probability argument now assigned independent literal-ensemble/proof/significance review; no full-literal refutation or formal dispatch. Configuration-model alternative incomplete.382558simple-homotopy nerve bridge unpaid and specific Barmak On Quillens theorem A for posets at people.kth.se/~jbarmak/thmafinal.pdf returned404: ENTIRE identified work ALL NEW hosts/versions/arxiv/authors/caches/mirrors/DOI/API/body/metadata UNAVAILABLE,no retry/alternate recovery. Distinct Kozlov original not denied.114ownfiles20raw/token/decodedbindings13frozen779savedhistorypaths verified;6GET attempts5PDFsuccess1HTTP404,3search9queries. Threeassignedoriginalsread,seventeenunread;nofigureaudit.57/60unchanged.'
den['root_r473_scope']=delta;denpath=ROOT/'inherited-denials-r477.json';save(denpath,den)
assert not R.exists();R.mkdir();(R/'inputs').mkdir();base=P/'expanded-corpus-r433'
for name in ['bootstrap.py','run.py','write_lane.py','verify_frozen.py','registry-roots.json','source_get_guard.py','model-policy-sol-only.json']:shutil.copyfile(base/name,R/name)
shutil.copyfile(ROOT/'charge_search.py',R/'charge_search.py');shutil.copyfile(denpath,R/'inherited-denials.json')
target=next(z for z in originals if z['object']['mathdb_id']==376636);literal=target['object']
(R/'inputs/original376636.raw.jsonl').write_bytes(target['raw'].encode());save(R/'inputs/literal376636.json',literal);save(R/'inputs/author-gates376636.json',gates['376636'])
s=(A/'ORDINARY-INVESTIGATION.md').read_text();(R/'inputs/author-proof376636.md').write_text(s[s.index('## 376636:'):])
for name in ['lp.pdf','lp.txt']:shutil.copyfile(A/'sources'/name,R/'inputs'/name)
for name in ['get-lp-plan.json','search3-response.txt']:shutil.copyfile(A/name,R/'inputs'/name)
shutil.copyfile(ROOT/'accepted57-review-context.json',R/'inputs/accepted57-scopes.json');prior=P/'spherical-error-monotonicity-source-review-sol-r1/inputs/prior39-routing.json';assert sha(prior)=='6493e29137d286242b09d96f97dfe39a9ca5146a8d73bcfa8177e4705d6aaff3';shutil.copyfile(prior,R/'inputs/prior39-scopes.json')
save(R/'reservation.json',dict(ids=[376636],rows=[literal],purpose='Independent full ordinary proof,random-ensemble/source scope and significance review,no formaltools or selfacceptance'))
(R/'reservation.sha256').write_text(sha(R/'reservation.json')+'  reservation.json\n');save(R/'search-budget.json',dict(calls_used=0,queries_used=0,maximum_calls=2,maximum_queries=6,charged_before_call=True))
task=f'''GPT-6.1 Sol high effort/default speed ONLY. Personally independently investigate MathDB376636 adaptive LP decoding convergence counterexample, exact source/random-ensemble scope and significance. No children,provider fallback,mathematical programs,formaltools,selfcredit. Current57/60 beyond39 prior,96total. Root orchestrates; you personally do the mathematics/source review.

FIRST shell command EXACTLY:
timeout 20 python3 -I -B {R}/bootstrap.py
Read COMPLETE printed TASK/AGENTS. SECOND command EXACTLY:
timeout 140 python3 -I -B {R}/verify_frozen.py before
No trailing punctuation/chaining. Bootstrap and standalone before/after verifiers explicit cap exceptions. ALL other substantive local work through immutable ABSOLUTE {R}/run.py UNIQUE_LABEL consuming Python stdin; all authored writes through immutable ABSOLUTE {R}/write_lane.py. Never rerun bootstrap/edit frozen helpers/inputs/TASK/caps. Preserve true failures, targeted repairs. Ordinary documentary typo/render/serialization failures do not by themselves mean access-policy breach; actual protected/frozen/access/budget/cap breach STOP/quarantine preserve evidence/no resets.

SOLE assigned376636. Active protected peers expanded-corpus-r474 and expanded-corpus-r475: NO read/stat/hash/list/glob/poll even metadata. NO history allowlist. Read ONLY own frozen inputs,own products,explicit PDF skill. No author lane,ROOT,campaign sibling/history files or embedded path follow. All formal/code-loop/Polynexus/crown/bunkbed/tournament/Hat bodies and flat integration basenames protected. r395/r463/r466 acquisitions/outputs quarantined,no reuse/refetch seeds. Trusted57+39 scope snapshots only bounded family context,no old certificate audit. All writes sole own lane,no/tmp/shared/parent/git/install/networkaccounts/publish/messages.

Read exact literal/raw JSONL and cached Taghavi-Siegel cs0703123 actual algorithm,standing code/channel conventions,one-sided initial bounds(15),all currently violated cuts,LP uniqueness,tie/degeneracy assumptions,iteration counting,Conjecture1 and all random-code/rate/degree/probability quantifiers. Source's random parity-check code distribution is not precisely specified by author report. Establish whether standing definitions select uniform matrices/configuration ensemble/connected or minimum-degree code ensemble,or genuinely quantify over all degree distributions/random ensembles. Do NOT silently identify an arbitrary relabeled disconnected forest with the intended ensemble,or exclude degree1 merely because simulations use regular codes. Exact source and material equation/glyph pages visually inspect via PDFskill /home/mj-kang/.codex/plugins/cache/openai-primary-runtime/pdf/26.1103.10131/skills/pdf/SKILL.md (announce/read). No PDFauthoring needed. Figures empirical context not theorem proof.

INDEPENDENTLY prove or break all parts of author path argument: lengthL repetition code,degree2 checks,LLR intervals gamma1(-3L,-2L),others(1,3/2),one-sided bounds,precise prefix LP optimizer at every round,which parity cuts fire when ALL added,absence of reverse/additional cuts,unbounded recession and uniqueness issues,termination count. Both box and actual one-bound formulations distinguished. A single rare objective is NOT a high-probability counterexample.
Pay actual probability bridge: fixedL depending on proposed universal alpha; b independent disjoint paths random relabeling,full-rank checkmatrix n=bL,m=b(L-1),positive fixedrate1/L; zero transmitted AWGN,independent Gaussian LLR positive density; event selection/orientation invariant or measurable under relabeling; conditional and unconditional independence,probability1-(1-pL)^b,globalLP factorization and synchronizing iteration count,unique optima or all-optimum robustness in other blocks. Handle n,m increase and order of constants/confidence quantifiers,rate/degree independence,alpha/beta conjunct; do not infer failure if alpha may depend on the chosen confidence or ensemble in a way source permits. All finite boundary/degeneracy cases paid. Author-only check is not your PASS.

Sustain credible intended-ensemble route beyond arbitrary relabeling if needed: author configuration-model sketch is UNPAID (isolated-path count/variance,degree constraints,simple/full-rank conditioning,cycle components). Personally close a uniform intended-model high-probability bridge if feasible with complete argument,no finite sweep or claimed concentration from expectation alone. Otherwise give precise lemma/scope GAP and separate valid auxiliary theorem from literal conjecture. A disconnected/degree-one omitted-domain correction earns zero discovery credit. Do not spend entire review on an ambiguous broad literal if source has a precise convention; investigate substantive admissible construction or park candidly.

PRIMARY qualification: cached original already acquired, no need refetch for basic model. Bounded current/final/correction and actual relevant prior comparison,reading real bodies. Copied search3-response is NAVIGATION only,not authenticated proof. It points to earlier cs0601099/ISIT2006 Adaptive Linear Programming Decoding (distinct version/work relationship must establish),an actual later thesis titled Decoding Linear Codes via Optimization and Graph-Based Techniques (search URL academia113173907),and later algorithm papers. These are not matching counterexample proof claims just because they give n-iteration upper bounds or modified algorithms; compare exact model/quantifiers/theorem content. At most bounded useful acquisition,not exhaustive literature sweep. No account/browser bypass. Every identified inherited unavailable work ALL NEW alternate delivery/version/body/metadata blocked,even if guard misses alias. In particular Barmak On Quillens theorem A for posets thmafinal.pdf404,LR0904.4778final redirect-only,virus1111.0531/2212.05733 final-body failures and registry metadata blocks all retained. Distinct decoding papers not automatically denied. No denied-work recovery.

Scientific significance: strongest positive case is bona fide high-probability failure of universal constant-iteration claim for an expressly admissible random ensemble; strongest negative is omitted-randomness/minimum-degree/connectivity repair or full prior-result adaptation. Shortness,standardtools/pathwitness alone not routine exclusion. Any routine exclusion needs COMPLETE applicable primary-to-model-to-target bridge,not keyword analogy. Specific matching unread primary theorem preciseHOLD; generic worldwideunknown not automatic veto. Bounded searchnonmatches not globalnovelty. Compare entire trusted57+39 bounded scopes; same coding vocabulary not family identity,allpath/block/rate/parameter variants onefamily. No acceptance/credit from an auxiliary deterministic lower bound or formalization.

NO mathematical programs/numerical tests/enumeration/experiments/CAS/solvers/Lean/compiler/checker/formalAPI. Personal ordinary proofs only; documentary/hash/source/PDF processing allowed under caps. Conditional DORMANT-SOL-FORMAL-PLAN only if full ordinary literal/scientific gates genuinely survive,with exact probabilistic objects,algorithm semantics,all bridges and full negation endpoint. No implementation/dispatch/selfacceptance. If ambiguity or hard intended-model bridge remains,deliver precise GAP instead of fabricated theorem.

Network: read ENTIRE supplied inherited-denials, recover material truncations BEFORE requests. Sole GETclient immutable source_get_guard.py UNDERrun.py. ONE manuallyselected exact persisted plan/invocation url/routes/destination/source_identity/purpose;routes['376636'],new own sources destination,identity/purpose>=12chars. Max8GETHOPS whole review,redirects charged. Max2native SEARCHcalls6exactquerystrings whole review. No customHTTP/curl/wget/requests/HEAD/nativeopenfetch/browser/API/account/POST/TLS/cookie/meta-refresh workaround. EVERYfailure identified work unavailable ALLnewhosts/versions/arxiv/authors/caches/mirrors/DOI/API/body/metadata;no retry,alternativeidentitycorrection or indirect recovery. Guard outcomes remain append-only,transport200nonpaper classified separately,no ledger rewriting.
BeforeEACHnative search persist exact queries-listplan via writer,authenticate LIVEoldcounter/ledger,precharge immutable ABSOLUTEcharge_search.py under runner; never manual counters/reset/refund. Save FULL actual response immediately before next research; supported text/JSON serialization,no btoa/TextEncoder. Serialization failure preserve and recover SAME response in memory,no extra networkcall. Search excerpts navigation not primary proof. Four exactregistry-rootmetadata artifacts unavailable,no refresh/reconstruction,not blanketban all distinct primary papers.

Capsaffinity<=2,childCPU115/supervisor120,AS6GiB,sampledgroupRSS6GiB,deadline130/outer140,arena2. Actual synchronous runner receipts/output/resources and reaping. Native/transient/writer/supervisor peaks unavailable,no universalcomplianceclaim. Standalone verifierCPU120exception,not under child115. No backgroundjobs.

Deliver REVIEW.md,independent PROOF.md or precise GAP.md,keyedreview.json376636 separate literal/source/ordinary/probability/prior/novelty/significance/family/formal/independent/procedure/acceptance gates,source-map,read/visual/access/search/resource inventories,objections and strongest contrary cases. Actual completed receipts/hashmanifest. Final standalone frozen-after then manifest EVERY own file/helpers/frozeninputs/reports/plans/payloads/responses/guard/searchledgers and EVERYcompletedreceiptJSON,with precisely named terminal noncircular exclusions,no subsequent frozen writes. No acknowledgment-only/acquisition-only handback. Credit0,57/60 unchanged pending root acceptance.
'''
(R/'TASK.txt').write_text(task);files=[q for q in R.iterdir() if q.is_file() and q.name!='search-budget.json']+list((R/'inputs').iterdir());save(R/'frozen-inputs.json',{str(q):sha(q) for q in files})
ready=dict(utc=now,lane=str(R),mathdb_id=376636,task_sha256=sha(R/'TASK.txt'),frozen_bindings=len(files),model='gpt-6.1-sol',reasoning='high',service='default',accepted_new=57,credit=0,protected_peers=['expanded-corpus-r474','expanded-corpus-r475'],source_copy_scope='Cleanr473 target-only exactliteral/authorargument/cachedactualsource,datednavigation and57+39scopes,no quarantined inputs')
save(ROOT/'adaptive-lp-review-r1-ready.json',ready);save(ROOT/'selection-routing-adaptive-lp-review-r1.json',dict(ids=[376636],sources=[literal['source_url']],lane=str(R),task_sha256=ready['task_sha256'],metadata_only=True));save(ROOT/'r473-barmak-boundary-delta.json',dict(utc=now,message=delta,immutable_worker_inputs_unchanged=True,new_protected_peer=R.name))
print(json.dumps(dict(manifest_files=114,original_bindings=20,frozen_bindings=13,receipt_exit_counts=record['receipt_exit_counts'],review=ready,accepted_new=57)))
