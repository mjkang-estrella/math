"""Root documentary integrity and disjoint metadata-only selection; no mathematics."""
import os,resource
os.sched_setaffinity(0,sorted(os.sched_getaffinity(0))[:2]);resource.setrlimit(resource.RLIMIT_CPU,(120,120));resource.setrlimit(resource.RLIMIT_AS,(6*1024**3,6*1024**3))
from pathlib import Path
import json,hashlib,datetime,collections,re,importlib.util,base64
P=Path(__file__).resolve().parent.parent;ROOT=P/'root-intake-r60';A=P/'expanded-corpus-r494'
def sha(q):return hashlib.sha256(q.read_bytes()).hexdigest()
def dg(b):return hashlib.sha256(b).hexdigest()
def read(q):return json.loads(q.read_text())
def save(q,d):
 assert not q.exists(),str(q)
 q.write_text(json.dumps(d,indent=2)+'\n')
now=datetime.datetime.now(datetime.timezone.utc).isoformat();assert read(P/'ledger.json')['accepted_new']==57
route=read(ROOT/'selection-routing-r494.json');assert sha(A/'TASK.txt')==route['task_sha256'] and sha(A/'reservation.json')==route['reservation_sha256']
m=read(A/'SHA256-MANIFEST.json');entries={v['path']:v for v in m['files']};assert len(entries)==len(m['files'])==99
for n,v in entries.items():
 assert not Path(n).is_absolute() and '..' not in Path(n).parts
 q=A/n;assert not q.is_symlink() and sha(q)==v['sha256'] and q.stat().st_size==v['bytes'],n
ex=m['terminal_noncircular_self_exclusions'];assert set(ex)=={'SHA256-MANIFEST.json','seal_manifest.receipt.json','seal_manifest.output.txt'}
actual=set()
for q in A.rglob('*'):
 assert not q.is_symlink()
 if q.is_file():actual.add(str(q.relative_to(A)))
assert actual==set(entries)|set(ex)
frozen=read(A/'frozen-inputs.json');assert len(frozen)==13 and all(Path(n).parent==A and sha(Path(n))==h for n,h in frozen.items())
after=read(A/'frozen-after.json');before=read(A/'frozen-before.json');assert before['count']==after['count']==13 and before['mismatches']==after['mismatches']==[]
gates=read(A/'results.json');prov=read(A/'original-bindings.json');ids=read(A/'reservation.json')['ids'];assert len(ids)==len(prov)==20 and set(ids)==set(map(int,gates))=={r['id'] for r in prov}
chunks={};sources={}
for row in prov:
 key=str(row['id']);q=Path(row['chunk']);assert q.is_relative_to(P.parent/'lanes/pi-mathdb-full-corpus-inventory-r301/corpus')
 if str(q) not in chunks:
  b=q.read_bytes();chunks[str(q)]=(dg(b),b.splitlines(keepends=True))
 h,lines=chunks[str(q)];assert h==row['chunk_sha256'];raw=lines[row['line']-1];obj=json.loads(raw)
 assert row['newline'] is True and raw.endswith(b'\n') and dg(raw)==row['raw_line_sha256'] and base64.b64decode(row['raw_line_base64'],validate=True)==raw and obj['mathdb_id']==row['id']
 tokens=re.findall(rb'"statement"\s*:\s*("(?:[^"\\]|\\.)*")',raw);assert len(tokens)==1;token=tokens[0]
 assert len(row['statement_tokens'])==1;st=row['statement_tokens'][0]
 assert token.decode()==st['token'] and dg(token)==st['token_sha256'] and json.loads(token)==obj['statement']==gates[key]['literal']['statement']==st['decoded'] and dg(obj['statement'].encode())==st['decoded_sha256'];sources[key]=obj['source_url']
receipts=[]
for q in sorted(A.glob('*.receipt.json')):
 v=read(q);assert v['cwd']==str(A) and v['cpu_limit_s']==115 and v['as_limit_bytes']==6*1024**3 and v['group_rss_guard_bytes']==6*1024**3 and v['deadline_s']==130 and len(v['affinity'])<=2 and v['killed'] is None
 receipts.append(dict(path=q.name,sha256=sha(q),exit=v['exit']))
assert read(A/'seal_manifest.receipt.json')['exit']==0
budget=read(A/'search-budget.json');assert budget==dict(calls_used=3,queries_used=9,maximum_calls=3,maximum_queries=9,charged_before_call=True)
charges=[json.loads(s) for s in (A/'search-charges.jsonl').read_text().splitlines()];assert len(charges)==3
prev=dict(calls_used=0,queries_used=0,maximum_calls=3,maximum_queries=9,charged_before_call=True)
for i,c in enumerate(charges,1):
 assert c['sequence']==i and c['before']==prev and sha(A/c['plan'])==c['plan_sha256'] and read(A/c['plan'])['queries']==c['queries']
 nxt=dict(prev,calls_used=i,queries_used=prev['queries_used']+len(c['queries']));assert c['after']==nxt;prev=nxt
 response=(A/f'search-{["one","two","three"][i-1]}-response.json').read_text();assert len(response)>1000
assert prev==budget and sha(A/'charge_search.py')==sha(ROOT/'charge_search.py')
events=[];prev='0'*64
plans={dg(json.dumps(read(q),sort_keys=True).encode()):read(q) for q in A.glob('get-*.json')}
for i,line in enumerate((A/'guard-ledger.jsonl').read_bytes().splitlines(keepends=True)):
 e=json.loads(line);assert e['seq']==i and e['previous']==prev;prev=dg(line);events.append(e)
 if e['event']=='success':
  q=A/e['destination'];assert sha(q)==e['sha256'] and q.stat().st_size==e['bytes']
 if e['event']=='attempt':assert e['plan_sha256'] in plans and '/server/api/' not in e['url'] and e['url'].startswith('https://') and set(e['routes'])<=set(map(str,ids))
counts=collections.Counter(e['event'] for e in events);assert counts==dict(attempt=5,success=5)
history=read(A/'history-access.json');allow=read(A/'historical-results-allowlist.json');assert len(history)==831
forbidden=('formal','code-loop','code_loop','polynexus','crown','bunkbed','tournament','hat-bipartite')
for x in history:
 rel=Path(x['path']).relative_to(P)
 assert not any(t in part.lower() for part in rel.parts for t in forbidden)
 assert not any(f'expanded-corpus-r{n}' in x['path'] for n in [395,463,466,482]) and x['path'] in allow and allow[x['path']]==x['sha256']
successes=[e for e in events if e['event']=='success'];assert sum((A/e['destination']).read_bytes().startswith(b'%PDF') for e in successes)==4
assert not any(e['event'] in {'redirect','unavailable'} for e in events)
summary='316875 AUTHOR full literal negation G=Z/4Z,x=(1,1,3,3),k2,w=(1,2),maxfiber2; every nonempty partial weight support/injection nonzero by mod2 or singleton2. Author actual final Hamidoune CPC17(2008)Conj2.2,p795,DOI10.1017/S0963548308009425 read/visually inspected, unrestricted weights retained with separate coprime branch. NOT independent PASS; significance/prior/novelty/family and formal gates unpaid. Strong positive full deliberate conjecture negation versus strong nonunit-domain-correction objection requires independent adjudication.322412 directed coloring recoloring/two-unit degree-reduction gaps unpaid.381003 author star upper bound not convex-roof lower bound; specific matching public counterclaim body acquired/read partly but measurement-to-convex-roof core/Lean declarations unread, public-proof HOLD not authenticated deep exclusion. Seventeen originals unread.99 own manifest files20 raw/token/decoded corpus bindings13 frozen831 saved historical names verified;5 GET successes4PDF1HTML,3 searches9 strings,no new denials.'
record=dict(utc=now,source_lane=str(A),task_reservation_genesis_verified=True,manifest_sha256=sha(A/'SHA256-MANIFEST.json'),verified_manifest_files=99,verified_original_bindings=ids,verified_frozen_bindings=13,source_url_by_id=sources,all20_gates=gates,runner_receipts=receipts,guard_events=dict(counts),search_budget=budget,root_disposition='ZERO_QUALIFIED_SURVIVORS_316875_ASSIGNED_INDEPENDENT_REVIEW',scientific_summary=summary,procedure='Own exhaustive manifest, corpus/token bindings, frozen inputs and831 saved historical names verified; root did not follow external history paths. All payload hashes/search continuity/plan hashes verified. Public Cambridge content/view route was an observed publisher PDF download consistent with earlier documentary rule, not permission for /server/api or arbitrary APIs. Sampled/native/transient/writer resource and read-depth qualifications retained; no universal process/body-read PASS.',credit=0,accepted_new=57,target_new=60,formal_dispatch=False,terminal_self_exclusions=ex,root_scope='Documentary integrity/routing only; no root mathematical solving/programs/Lean/checkers.')
den=read(ROOT/'inherited-denials-r504.json');den['utc']=now;den['root_r494_scope']=summary;denpath=ROOT/'inherited-denials-r505.json'
# All verification precedes documentary writes or review preparation.
save(P/'expanded-corpus-r494-parent-integration.json',record);save(denpath,den)
import shutil
R=P/'weighted-zero-sum-source-review-sol-r1';assert not R.exists();R.mkdir();(R/'inputs').mkdir()
for name in ['bootstrap.py','run.py','write_lane.py','verify_frozen.py','registry-roots.json','source_get_guard.py','model-policy-sol-only.json','charge_search.py']:shutil.copyfile(A/name,R/name)
shutil.copyfile(denpath,R/'inherited-denials.json')
prow=next(r for r in prov if r['id']==316875);raw=base64.b64decode(prow['raw_line_base64'],validate=True);literal=json.loads(raw)
(R/'inputs/original316875.raw.jsonl').write_bytes(raw);save(R/'inputs/provenance316875.json',prow);save(R/'inputs/literal316875.json',literal);save(R/'inputs/author-gates316875.json',gates['316875'])
for name in ['FULLCANDIDATE.md','DORMANT-SOL-FORMAL-PLAN.md','SUSTAINED-DERIVATIONS.md','get-weighted.json','get-weighted-final.json','search-one-response.json','search-two-response.json','search-three-response.json']:shutil.copyfile(A/name,R/'inputs'/name)
for name in ['weighted.pdf','weighted.txt','weighted-final.pdf','weighted-final.txt','weighted-final-p795.png']:shutil.copyfile(A/'sources'/name,R/'inputs'/name)
shutil.copyfile(ROOT/'accepted57-review-context.json',R/'inputs/accepted57-scopes.json');prior=P/'spherical-error-monotonicity-source-review-sol-r1/inputs/prior39-routing.json';assert sha(prior)=='6493e29137d286242b09d96f97dfe39a9ca5146a8d73bcfa8177e4705d6aaff3';shutil.copyfile(prior,R/'inputs/prior39-scopes.json')
precedent=P/'cyclic-unit-fixed-sums-source-review-sol-r1'
for name in ['REVIEW.md','PROOF.md']:shutil.copyfile(precedent/name,R/'inputs'/('domain-precedent316244-'+name))
save(R/'reservation.json',dict(ids=[316875],rows=[literal],purpose='Independent full literal weighted-zero-sum counterexample, actual final-source and substantive/domain-correction qualification; no formal tools'))
(R/'reservation.sha256').write_text(sha(R/'reservation.json')+'  reservation.json\n');save(R/'search-budget.json',dict(calls_used=0,queries_used=0,maximum_calls=2,maximum_queries=6,charged_before_call=True))
task=f'''Use ONLY GPT-6.1 Sol, high effort, default speed. Personally perform independent full ordinary-proof, exact original/final-source, current primary-prior and SIGNIFICANCE review of MathDB316875 weighted zero-sum conjecture. No children/fallback/mathematical programs/enumeration/numerical tests/CAS/solver/Lean/compiler/checker/formal APIs or self-credit. Root orchestrates, you do mathematical qualification. Complete bounded review, not acquisition-only. Current57/60 beyond39,96 total. No formal implementation/dispatch.

FIRST shell command EXACTLY:
timeout 20 python3 -I -B {R}/bootstrap.py
Read COMPLETE printed TASK/AGENTS. SECOND shell command EXACTLY:
timeout 140 python3 -I -B {R}/verify_frozen.py before
No punctuation/chaining. Bootstrap/standalone verifiers are explicit cap exceptions. EVERY other substantive local shell/document/PDF/source operation immutable ABSOLUTE {R}/run.py UNIQUE_LABEL Python stdin with timeout140; authored writes immutable ABSOLUTE {R}/write_lane.py. Never edit frozen helpers/inputs/TASK/caps or rerun bootstrap. Preserve failures; fresh diagnostic repair allowed. Actual protected/frozen/access/guard/counter/cap breach STOP/quarantine/no reset, while documentary typo/render/serialization failure is not automatically a breach.

SOLE316875. Protected active peers expanded-corpus-r495 and tree-reconstruction-radius-source-review-sol-r1 ENTIRELY including metadata/stat/read/hash/list/glob/poll/reservations/flat integrations. Own supplied inputs/products and explicit PDF skill ONLY. No author/ROOT/campaign/sibling/history/embedded-path reads, no historical allowlist. All formal/code-loop/Polynexus/crown/bunkbed/tournament/Hat bodies AND flat integrations protected. ENTIRE r395/r463/r466/r482 packets permanently quarantined; no reuse/refetch seeds. No shared/parent/tmp writes/git/install/publication/accounts/browser/external messages. Trusted supplied57+39 statement scopes only, no upstream truth/certificate audit.

Read exact raw/literal and personally independently reconstruct the whole no-sum proof BEFORE opening FULLCANDIDATE.md; then adversarially audit it. Mechanism disclosed in task, so independent verification is not independent invention. Target finite abelian group order n, x in G^n, integer weight list w of length k, max fiber of x<=k, existential NONEMPTY subset I of weight positions and injection f:I→[1,n], sum w_i*x_f(i)=0 using integer group scalar action. Do not confuse k with support size, fixed-length/full-weight sum with variable nonempty partial subset, or integer scalar multiplication with a field. Inspect ALL quantifiers, hidden gcd/unit/sum-of-weights/prime/exponent hypotheses in actual source setup, n=cardG and index conventions. A self-contained table/case lemma is insufficient without literal group/multiplicity/partial-injection bridge.

Author witness G=Z/4Z,n4,k2,x=(1,1,3,3),w=(1,2). If first weight in I, mod2 image is1; if absent, nonempty I forces singleton second weight and 2*x=2mod4. Independently verify ALL admissible nonempty supports and every injection, exact maximum fiber2/length4/integer action, group admissibility and genuine negation. Even arbitrary noninjective choices cannot help according to author; prove correct quantification rather than assert finite check. Odd square modulus examples belong to SAME obstruction family, not separate credit. Author failed padding/multiplicity routes are in SUSTAINED-DERIVATIONS.md; audit only relevant argument. No execution/enumeration to establish elementary mathematics.

Source: original Hamidoune0711.4074v1 Conjecture5 and actual final Cambridge CPC17(2008)793–798 DOI10.1017/S0963548308009425, Conjecture2.2 p795, supplied both PDF/text and own author page render. Read full six-page final body, actual original relevant setup/proof and conjecture, not merely author quotation. Inspect preceding weighted lemma, following coprime-weight branch and exact surrounding assumptions; determine whether unrestricted integer weights are deliberate. Author says final retains them and explicitly treats coprime case separately. Material source glyphs/quantifiers must be personally visually checked. Use/announce/read PDF skill /home/mj-kang/.codex/plugins/cache/openai-primary-runtime/pdf/26.1103.10131/skills/pdf/SKILL.md. Native read-only presentation of PERMITTED own rendered pages is explicitly allowed outside runner, but creation/conversion/source processing under runner and no filesystem code outside caps. Native/transient/writer/supervisor peaks unknown; no universal resource PASS. No PDF authoring or installs.

SIGNIFICANCE IS A CENTRAL UNPAID GATE, not a formality. Strong positive case: full literal and actual final deliberately unrestricted conjecture negated; separate known coprime branch means this is not a corpus typo or automatically an even-modulus domain mistake. Root standard does not exclude a short counterexample merely for smallness. Strong contrary case: nonunit-weight quotient obstruction may expose only an omitted natural unit hypothesis and thus constitute prohibited domain correction, or be a complete routine adaptation of a known weighted-zero-sum result. Assess exact new structural content versus elementary hypothesis repair, with precise arguments on BOTH sides. No acceptance from open label/empty solutions, no rejection merely from shortness/standard tools. Give a definite reasoned recommendation or exact unresolved adjudication gap.

Copied domain-precedent316244 REVIEW/PROOF concerns fixed-length sums of DISTINCT cyclic UNITS with an even-modulus parity obstruction; root excluded that prior route as domain correction (not an accepted result). It is a comparison precedent ONLY, not target316875 and not an automatic exclusion. Distinguish arbitrary integer weights on sequences of bounded multiplicity from summing all distinct units, and account for author's odd-square variant instead of equating every parity argument. Do not follow embedded blocked source paths. That earlier ENTIRE0704.0541/JCTA10.1016/j.jcta.2007.12.007 work remains unavailable for new delivery; copied review evidence only. Final current target0711.4074 is a DISTINCT work, supplied clean actual final body, not blanket denied by common author/topic.

Prior/public gate: inspect actual applicable primary theorems/proofs rather than abstracts/search snippets. Distinguish prescribed finite weight list and partial injective pairing from A-weighted zero-sums, Caro's zero-total-weight full pairing, Gao/Davenport n+D−1 statements and unit-only weighted theorems. If public/routine exclusion, give COMPLETE theorem/proof-to-target bridge with EVERY hypothesis and the exact counterexample/reduction. No source-own/public label without actual body, no earlier printed exact witness unless authenticated. Specific identified applicable unread proof is HOLD; generic worldwide unknown not automatic veto; bounded nonmatches not novelty. Author searches saved as navigation only, no matching earlier proof authenticated. Compare supplied57+39 exact scopes, one family all modulus/weight/root variants/helpers/formalizations, no certificate audit. Conditional dormant Sol formal plan ONLY if full ordinary/literal and substantive scientific gates prospectively survive; otherwise document exclusion/GAP, not formal dispatch.

Read COMPLETE inherited-denials and recover material truncations BEFORE network. Cached original/final provided; do not reacquire absent concrete need. Sole GET immutable ABSOLUTE source_get_guard.py UNDER own run.py, ONE persisted manually chosen exact plan/invocation, route['316875'], actual observed primary URL, NEW own sources destination, source_identity/purpose>=12 characters. Max6 guarded GET HOPS including redirects and max2 native SEARCH calls/6 exact querystrings for this separate review. Before EACH search persist exact queries-list plan through writer, read LIVE counter/ledger, precharge immutable ABSOLUTE charge_search.py under runner. Save FULL actual response immediately before further work as ordinary JSON/string, no btoa/TextEncoder. Local persistence error may recover SAME in-memory response without another call. No reset/refund/manual counters. Search navigation is not proof.

NO APIs incl /server/api/ bitstreams, custom HTTP/curl/wget/requests/HEAD/native URLopen/browser/accounts/POST/TLS/cookie/JS/meta-refresh workarounds. Every failed identified work ALL NEW hosts/versions/arxiv/authors/cache/mirror/DOI/API/body/METADATA deliveries unavailable, no retry/HTTPS upgrade/alternate identity/indirect recovery. Guard rejection STOP, preserve failed true exit and ledger, no unavailable-row backfill/reset. All inherited closures apply, including original PageRank, Csaji ALT2010, Ni-Tatikonda0809.0158 and prior cyclic-unit0704.0541; distinct actual target not itself denied. Four registry ROOT metadata artifacts unavailable; no README/tree/API/branch/version/mirror refresh/reconstruction. Transport200 nonpaper not primary-body PASS. No network after a required stop.

Caps affinity<=2,childCPU115/supervisor120,AS6GiB,sampled processgroupRSS6GiB,deadline130/outer140,arena2. Standalone verifierCPU120 exception not nested under child115. All processes synchronous with true exits/resources/reaping; no background jobs. Native/writer/transient peaks unknown, no universal cgroup/process-cap certification.

Deliver REVIEW.md, independently constructed PROOF.md or precise GAP.md, keyed review.json316875 separate literal/source/ordinary/prior/novelty/significance/family/formal/independent/procedure/acceptance gates, strongest opposing cases, full primary reduction or precise nonmatch, source map, read/visual/access/search/resource inventories and receipts. Dormant formal blueprint only if warranted, faithful finite-group/integer-action/fiber/subtype-injection-to-universal-negation bridge, audits/replay/paper; no implementation. Final standalone verify_frozen.py after THEN exhaustive own-file manifest including ALL frozen helpers/inputs/plans/payloads/full search responses/ledgers/ALL completed receipt JSON, exact terminal noncircular exclusions, no later frozen writes. Credit0,57/60 unchanged pending root acceptance.
'''
(R/'TASK.txt').write_text(task);ff=[q for q in R.iterdir() if q.is_file() and q.name!='search-budget.json']+list((R/'inputs').iterdir());save(R/'frozen-inputs.json',{str(q):sha(q) for q in ff})
ready=dict(utc=now,lane=str(R),mathdb_id=316875,task_sha256=sha(R/'TASK.txt'),frozen_bindings=len(ff),model='gpt-6.1-sol',reasoning='high',service='default',accepted_new=57,credit=0,protected_peers=['expanded-corpus-r495','tree-reconstruction-radius-source-review-sol-r1'])
save(ROOT/'weighted-zero-sum-review-r1-ready.json',ready);save(ROOT/'selection-routing-weighted-zero-sum-review-r1.json',dict(ids=[316875],sources=[literal['source_url']],lane=str(R),task_sha256=ready['task_sha256'],metadata_only=True));save(ROOT/'r494-completion-boundary-delta.json',dict(utc=now,message=summary,new_protected_peer=R.name,immutable_worker_inputs_unchanged=True))
print(json.dumps(dict(files=99,frozen=13,bindings=20,receipts=len(receipts),guard_events=dict(counts),search_budget=budget,review=ready,credit=0,accepted_new=57)))
