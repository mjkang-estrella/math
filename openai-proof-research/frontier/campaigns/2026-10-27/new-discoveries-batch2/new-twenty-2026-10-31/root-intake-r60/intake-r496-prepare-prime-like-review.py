"""Root documentary integrity and disjoint metadata-only selection; no mathematics."""
import os,resource
os.sched_setaffinity(0,sorted(os.sched_getaffinity(0))[:2]);resource.setrlimit(resource.RLIMIT_CPU,(120,120));resource.setrlimit(resource.RLIMIT_AS,(6*1024**3,6*1024**3))
from pathlib import Path
import json,hashlib,datetime,collections,re,importlib.util
P=Path(__file__).resolve().parent.parent;ROOT=P/'root-intake-r60';A=P/'expanded-corpus-r496'
def sha(q):return hashlib.sha256(q.read_bytes()).hexdigest()
def dg(b):return hashlib.sha256(b).hexdigest()
def read(q):return json.loads(q.read_text())
def save(q,d):
 assert not q.exists(),str(q)
 q.write_text(json.dumps(d,indent=2)+'\n')
now=datetime.datetime.now(datetime.timezone.utc).isoformat();assert read(P/'ledger.json')['accepted_new']==57
route=read(ROOT/'selection-routing-r496.json');assert sha(A/'TASK.txt')==route['task_sha256'] and sha(A/'reservation.json')==route['reservation_sha256']
m=read(A/'MANIFEST.sha256.json');entries=m['files'];assert len(entries)==132
for n,h in entries.items():
 assert not Path(n).is_absolute() and '..' not in Path(n).parts
 q=A/n;assert not q.is_symlink() and sha(q)==h,n
ex=m['terminal_noncircular_self_exclusions'];assert set(ex)=={'MANIFEST.sha256.json','terminal-manifest.receipt.json','terminal-manifest.output.txt'}
actual=set()
for q in A.rglob('*'):
 assert not q.is_symlink()
 if q.is_file():actual.add(str(q.relative_to(A)))
assert actual==set(entries)|set(ex)
frozen=read(A/'frozen-inputs.json');assert len(frozen)==13 and all(Path(n).parent==A and sha(Path(n))==h for n,h in frozen.items())
after=read(A/'frozen-after.json');before=read(A/'frozen-before.json');assert before['count']==after['count']==13 and before['mismatches']==after['mismatches']==[]
gates=read(A/'results.json');prov=read(A/'provenance.json');ids=read(A/'reservation.json')['ids'];assert len(ids)==len(prov)==20 and set(ids)==set(map(int,gates))==set(map(int,prov))
chunks={};sources={}
for key,row in prov.items():
 q=Path(row['chunk']);assert q.is_relative_to(P.parent/'lanes/pi-mathdb-full-corpus-inventory-r301/corpus')
 if str(q) not in chunks:
  b=q.read_bytes();chunks[str(q)]=(dg(b),b.splitlines(keepends=True))
 h,lines=chunks[str(q)];assert h==row['chunk_sha256'];raw=lines[row['line']-1];obj=json.loads(raw)
 assert row['newline'] is True and raw.endswith(b'\n') and dg(raw)==row['raw_sha256'] and (A/'originals'/f'{key}.jsonl').read_bytes()==raw and obj['mathdb_id']==int(key)
 tokens=re.findall(rb'"statement"\s*:\s*("(?:[^"\\]|\\.)*")',raw);assert len(tokens)==1;token=tokens[0]
 assert token.decode()==row['statement_token'] and dg(token)==row['statement_token_sha256'] and json.loads(token)==obj['statement']==gates[key]['literal']['statement']==row['decoded_statement'] and dg(obj['statement'].encode())==row['decoded_utf8_sha256'];sources[key]=obj['source_url']
receipts=[]
for q in sorted(A.glob('*.receipt.json')):
 v=read(q);assert v['cwd']==str(A) and v['cpu_limit_s']==115 and v['as_limit_bytes']==6*1024**3 and v['group_rss_guard_bytes']==6*1024**3 and v['deadline_s']==130 and len(v['affinity'])<=2 and v['killed'] is None
 receipts.append(dict(path=q.name,sha256=sha(q),exit=v['exit']))
assert read(A/'terminal-manifest.receipt.json')['exit']==0
budget=read(A/'search-budget.json');assert budget==dict(calls_used=3,queries_used=9,maximum_calls=3,maximum_queries=9,charged_before_call=True)
charges=[json.loads(s) for s in (A/'search-charges.jsonl').read_text().splitlines()];assert len(charges)==3
prev=dict(calls_used=0,queries_used=0,maximum_calls=3,maximum_queries=9,charged_before_call=True)
for i,c in enumerate(charges,1):
 assert c['sequence']==i and c['before']==prev and sha(A/c['plan'])==c['plan_sha256'] and read(A/c['plan'])['queries']==c['queries']
 nxt=dict(prev,calls_used=i,queries_used=prev['queries_used']+len(c['queries']));assert c['after']==nxt;prev=nxt
 response=(A/f'search-{["one","two","three"][i-1]}-response.json').read_text();assert len(response)>1000
assert prev==budget and sha(A/'charge_search.py')==sha(ROOT/'charge_search.py')
events=[];prev='0'*64
plans={dg(json.dumps(read(q),sort_keys=True).encode()):read(q) for q in A.glob('get-*-plan.json')}
for i,line in enumerate((A/'guard-ledger.jsonl').read_bytes().splitlines(keepends=True)):
 e=json.loads(line);assert e['seq']==i and e['previous']==prev;prev=dg(line);events.append(e)
 if e['event']=='success':
  q=A/e['destination'];assert sha(q)==e['sha256'] and q.stat().st_size==e['bytes']
 if e['event']=='attempt':assert e['plan_sha256'] in plans and '/server/api/' not in e['url'] and e['url'].startswith('https://') and set(e['routes'])<=set(map(str,ids))
counts=collections.Counter(e['event'] for e in events);assert counts==dict(attempt=6,success=6)
history=read(A/'history-access.json');allow=read(A/'historical-results-allowlist.json');assert len(history)==838
forbidden=('formal','code-loop','code_loop','polynexus','crown','bunkbed','tournament','hat-bipartite')
for x in history:
 rel=Path(x['path']).relative_to(P)
 assert not any(t in part.lower() for part in rel.parts for t in forbidden)
 assert not any(f'expanded-corpus-r{n}' in x['path'] for n in [395,463,466,482]) and x['path'] in allow and allow[x['path']]==x['sha256']
assert sum((A/e['destination']).read_bytes().startswith(b'%PDF') for e in events if e['event']=='success')==5
summary='368088 author proposed FULL ordinary negation of arbitrary-Q prime-like Goldbach: injective prime>3 map fixes1mod6 and subtracts1 on5mod6; disjoint image branches, exact all-cutoff counting discrepancy<=2<3, allQ1mod3 so arbitrarily large even multiples6 excluded. Actual2025v1 Definition1/Conj1 visually read, matching2023 companion read; current source metadata onlyv1/no journal displayed does not prove absence of final/corrections. NOT independent PASS; prior/significance/family/formal qualification unpaid, assigned independent review.381001 actual Rahiminia-Amini2008 Th1/2 proof exact public0.358026 restricted positive-branch calculus does not pay stripk-2<z<k-1; unrestricted negative-real objection correction0, earlier broad positive-range claim corrected. Seventeen originals unread.132 files20 raw/token/decoded corpus bindings13 frozen838 saved historical names verified;6GET successes5PDF1HTML,3 searches9 strings,no new denial. Orchestration JS syntax error dispatched no shell, reading/truncation recovery/native-transient-writer limits retained.'
record=dict(utc=now,source_lane=str(A),task_reservation_genesis_verified=True,manifest_sha256=sha(A/'MANIFEST.sha256.json'),verified_manifest_files=132,verified_original_bindings=ids,verified_frozen_bindings=13,source_url_by_id=sources,all20_gates=gates,runner_receipts=receipts,guard_events=dict(counts),search_budget=budget,root_disposition='ZERO_QUALIFIED_SURVIVORS_368088_ASSIGNED_INDEPENDENT_REVIEW',scientific_summary=summary,credit=0,accepted_new=57,target_new=60,formal_dispatch=False,terminal_self_exclusions=ex,root_scope='Documentary provenance/integrity/routing only; no root mathematical solving/programs/Lean/checkers.')
den=read(ROOT/'inherited-denials-r508.json');den['utc']=now;den['root_r496_scope']=summary;denpath=ROOT/'inherited-denials-r509.json'
# All checks precede root integration and target-only review preparation.
save(P/'expanded-corpus-r496-parent-integration.json',record);save(denpath,den)
import shutil
R=P/'prime-like-goldbach-source-review-sol-r1';assert not R.exists();R.mkdir();(R/'inputs').mkdir()
for name in ['bootstrap.py','run.py','write_lane.py','verify_frozen.py','registry-roots.json','source_get_guard.py','model-policy-sol-only.json','charge_search.py']:shutil.copyfile(A/name,R/name)
shutil.copyfile(denpath,R/'inherited-denials.json')
literal=json.loads((A/'originals/368088.jsonl').read_text());shutil.copyfile(A/'originals/368088.jsonl',R/'inputs/original368088.raw.jsonl');save(R/'inputs/provenance368088.json',prov['368088']);save(R/'inputs/literal368088.json',literal);save(R/'inputs/author-gates368088.json',gates['368088'])
for name in ['FULLCANDIDATE.md','DORMANT-SOL-FORMAL-PLAN.md','SUSTAINED-DERIVATIONS.md','get-goldbach-plan.json','get-goldbach-metadata-plan.json','get-companion-goldbach-plan.json','search-one-response.json','search-two-response.json','search-three-response.json']:shutil.copyfile(A/name,R/'inputs'/name)
for name in ['goldbach.pdf','goldbach.txt','goldbach-companion.pdf','goldbach-companion.txt','goldbach-current.html','goldbach-p3.png','goldbach-p5.png']:shutil.copyfile(A/'sources'/name,R/'inputs'/name)
shutil.copyfile(ROOT/'accepted57-review-context.json',R/'inputs/accepted57-scopes.json');prior=P/'spherical-error-monotonicity-source-review-sol-r1/inputs/prior39-routing.json';assert sha(prior)=='6493e29137d286242b09d96f97dfe39a9ca5146a8d73bcfa8177e4705d6aaff3';shutil.copyfile(prior,R/'inputs/prior39-scopes.json')
save(R/'reservation.json',dict(ids=[368088],rows=[literal],purpose='Independent full arbitrary-prime-counting-distribution Goldbach negation, literal/actual-source and substantive/prior qualification; no formal tools'))
(R/'reservation.sha256').write_text(sha(R/'reservation.json')+'  reservation.json\n');save(R/'search-budget.json',dict(calls_used=0,queries_used=0,maximum_calls=2,maximum_queries=6,charged_before_call=True))
task=f'''Use ONLY GPT-6.1 Sol, high effort, default speed. Personally independently review MathDB368088 full ordinary counterexample, exact source definition/quantifiers, current primary prior and SIGNIFICANCE. No children/fallback/mathematical programs/enumeration/numerical experiments/CAS/solver/Lean/compiler/checker/formal API or self-credit. Root orchestrates, you do mathematics/source qualification. Complete bounded investigation, not acquisition-only.57/60 beyond39 prior,96 total unchanged. No formal dispatch.

FIRST shell command EXACTLY:
timeout 20 python3 -I -B {R}/bootstrap.py
Read COMPLETE printed TASK/AGENTS. SECOND shell command EXACTLY:
timeout 140 python3 -I -B {R}/verify_frozen.py before
No punctuation/chaining. Bootstrap/standalone verifiers explicit cap exceptions. Every other substantive local shell/document/source/PDF operation immutable ABSOLUTE {R}/run.py UNIQUE_LABEL Python stdin with timeout140; authored writes immutable ABSOLUTE {R}/write_lane.py. Never edit frozen helpers/inputs/TASK/caps or rerun bootstrap. Preserve failures; targeted fresh diagnostic repair allowed. Actual protected/frozen/access/guard/counter/cap breach STOP/quarantine/no reset. Documentary typo/render/serialization failure is not automatically a breach.

SOLE368088. Protected active peers expanded-corpus-r497 and expanded-corpus-r498 ENTIRELY including metadata/stat/read/hash/list/glob/poll/reservations/flat integrations. Own supplied inputs/products and explicit PDF skill ONLY, no ROOT/author/campaign/sibling/history/embedded-path access. No historical allowlist. All formal/code-loop/Polynexus/crown/bunkbed/tournament/Hat bodies AND flat integrations protected. ENTIRE r395/r463/r466/r482 permanently quarantined; no reuse/refetch seeds. No shared/parent/tmp writes/git/install/publication/accounts/browser/external messages. Supplied57+39 exact scope records trusted, no upstream truth/certificate audit.

Read exact raw/literal first and independently reconstruct the proof BEFORE opening FULLCANDIDATE.md; then adversarially audit it. Mechanism disclosed in task, independent verification is not independent invention. Target is an ARBITRARY subset Q of natural numbers whose counting function differs from prime counting by a fixed natural constant under STRICT absolute inequality for EVERY INTEGER cutoff. It asserts eventual representation of every sufficiently large even integer by TWO Q elements. Not classical prime Goldbach, not just translates of primes, not merely density asymptotics. Inspect exact natural/integer/coercion/0/infinite-set conventions, c>0 versus c inN, eventual quantifier, whether q1=q2 allowed, sum restrictions, random/residue/admissibility/primality standing assumptions and any source constraints omitted from corpus. Literal has a stray c\\ta typesetting token: recover actual source, no credit for typo alone.

Actual provided source: Farhadian2504.14353v1 Definition1 p3, Definition2 p4, Conjecture1 p5 and surrounding proofs/probability argument/conclusion; provided distinct Farhadian–Fanai2211.02865v2 Definition1 p2 and Conjecture1 p5, actual full body. Personally read both relevant whole short manuscripts, not author's assertions. They deliberately describe nonprime arbitrary Q according to author. Determine whether any standing local admissibility/randomness condition changes domain. Source current arXiv metadata supplied has onlyv1/no displayed journal reference as retrieved recently; that does not prove no publication/correction. Current final/version/correction qualification bounded actual evidence, not generic impossible worldwide absence. This work itself not denied; no unneeded reacquisition of supplied bodies. Both manuscript endpoints are ONE family, not separate credit.

Author construction to verify AFTER independent reconstruction: let P*={{primes p>3}}. Primality gives residue1or5mod6. Define f(p)=p for1mod6, f(p)=p−1 for5mod6; Q=image f. Branch images1/4mod6 disjoint, each branch injective, positive. All Q1mod3. For every integer cutoff n>=3, pi_Q(n)=pi(n)−2+epsilon(n), epsilon1 iff n+1 is prime5mod6. Prime p>n contributes only that possible boundary point; prove both directions and injective image cardinality, not bounded displacement alone. Small n0,1,2 and negatives handled, strictc3 bound from error<=2. Review every cutoff and each exceptional prime2/3, image positivity and any source infinitude requirement; use elementary valid proof if needed rather than assume source omits it. No prime number theorem, Goldbach assumption or unproved prime-pattern hypothesis. Actual finite counting-set bijection must be paid; complete integral inequalities/coercions, not informal asymptotics.

For every proposed natural N choose n=3(N+1), even2n=6(N+1)>N but every Q+Q2mod3. Pay full arbitrary-large negation, not one small exception. Repetition q1=q2 still obeys modular obstruction; account for source distinctness if any. Author failed nearest-multiple3 rounding merged twins, so bounded movement alone did not prove bounded counting discrepancy; selected disjoint branch map fixes exactly that. Uniform-shift translation lemma conditional on classical Goldbach is NOT the counterexample. Alternative0/3mod6 rounding is same family/no extra credit. If source hidden assumptions defeat witness, repair concretely or precise GAP, no silent strengthened/weakened question.

Use/announce/read PDF skill /home/mj-kang/.codex/plugins/cache/openai-primary-runtime/pdf/26.1103.10131/skills/pdf/SKILL.md. Personally visually inspect material actual definitions/conjecture quantified constants/allintegercutoffs/arbitraryQ/no-prime assumption and companion glyphs, not text extraction or author renders alone. Native read-only presentation of PERMITTED own rendered pages explicitly allowed outside runner; creation/conversion/source processing under runner, no filesystem code outside caps, native/transient/writer/supervisor peaks unknown. No PDF authoring/install.

SIGNIFICANCE central unpaid gate. Strong positive case: full deliberately stated universal generalized conjecture in2023/2025 sources falsified under their EXACT bounded-discrepancy definition, shows counting distribution alone cannot determine additive coverage, no MathDB mistranscription/finite endpoint repair and not classical Goldbach claim. Short proof/small modulus alone not exclusion. Strong contrary case: one residue obstruction may merely expose a missing natural local-admissibility condition in an overbroad 'prime-like' domain, with no advance in a corrected substantive problem; standard bounded-displacement/additive-combinatorics results may fully subsume it. Campaign excludes domain corrections and complete routine adaptations. Make precise reasoned recommendation on actual new structural content and BOTH opposing cases. Do not accept just an open label or reject just familiar tools. If routine/public exclusion, read actual primary theorem/proof and give COMPLETE hypothesis/conclusion-to-target bridge; no earlier printed exact refutation or matching theorem from snippets alone. Domain-correction policy judgment is distinct from a demonstrated public-prior exclusion and must be labelled honestly.

No specifically matching earlier body authenticated by author, three saved searches navigation only. Inspect relevant actual primary proof/counterclaim if identified, compare source translation lemma/distribution definition to construction, current-version/source/correction evidence and concrete novelty claims. Specific applicable unread proof => precise HOLD; generic worldwide unknown not automatic veto, bounded nonmatches not novelty. Four registry ROOT artifacts remain unavailable, no README/tree/API/branch/version/mirror refresh/reconstruction. Compare ALL supplied57+39 exact scopes, not topic words; parity/prime/Goldbach/helpers/coefficient terms alone not duplicates. Fullpersonalcomparison must be paid through recovered scope fields, file loading alone insufficient.

Network read COMPLETE inherited-denials before requests, recover material truncations. Sole GET immutable ABSOLUTE source_get_guard.py UNDER own run.py, ONE manually chosen persisted exact plan/invocation, route['368088'], actual observed primary URL, NEW own sources destination, source_identity/purpose>=12chars. Max6 GET HOPS including redirects, max2 native SEARCH calls/6 exact querystrings for this independent review. Before EACH search persist exact queries-list plan through writer, read LIVE counters/ledger, precharge immutable ABSOLUTE charge_search.py under runner, save FULL actual response immediately before further work ordinary JSON/string, no btoa/TextEncoder. Local serialization failure may recover SAME in-memory response, no extra source call. No counter reset/refund/manual edits. Search is navigation not proof.

NO APIs including /server/api/ bitstreams, customHTTP/curl/wget/requests/HEAD/native URLopen/browser/accounts/POST/TLS/cookie/JS/meta-refresh workarounds. Every identified failed work ALL NEW hosts/versions/arxiv/authors/cache/mirror/DOI/API/body/METADATA unavailable, no retry/HTTPSupgrade/alternate identity/indirect recovery. Guard rejection STOP with true failure receipt and immutable ledger, no unavailable-row backfill/reset. All inherited whole-work closures apply; do not blanket deny distinct papers. PageRank/Csaji/Ni-Tatikonda/FNJ/cyclic-unit0704.0541 closures remain. Transport200 nonpaper not primary-body PASS. No network or mathematical investigation after required STOP.

Caps affinity<=2,childCPU115/supervisor120,AS6GiB,sampledgroupRSS6GiB,deadline130/outer140,arena2. Standalone verifierCPU120 exception not nested under child115. All subprocesses synchronous with true exits/resources/reaping; no background jobs. Native/writer/transient/supervisor peaks unknown, no universal cgroup/process-cap assertion.

Deliver REVIEW.md, independent PROOF.md or precise GAP.md, keyed review.json368088 separate literal/source/ordinary/prior/novelty/significance/family/formal/independent/procedure/acceptance gates; strongest objections/full prior bridge or precise nonmatch; source map, read/visual/access/search/resource inventories and receipts. Conditional dormant Sol formal blueprint ONLY if full ordinary/literal/scientific gates prospectively survive: actual prime-residue map, injectivity, count bijections/allcutoffs/strictbound and eventual modular negation, exact source bridge, permitted axioms/audit/replay/paper obligations. No implementation/dispatch/selfcredit. Final standalone verify_frozen.py after THEN exhaustive own-file SHA manifest including ALL helpers/frozeninputs/plans/payloads/fullresponses/ledgers/ALL completed receiptJSON, exact terminal noncircular exclusions, no later frozenwrites. Credit0,57/60 unchanged pending root acceptance.
'''
(R/'TASK.txt').write_text(task);ff=[q for q in R.iterdir() if q.is_file() and q.name!='search-budget.json']+list((R/'inputs').iterdir());save(R/'frozen-inputs.json',{str(q):sha(q) for q in ff})
ready=dict(utc=now,lane=str(R),mathdb_id=368088,task_sha256=sha(R/'TASK.txt'),frozen_bindings=len(ff),model='gpt-6.1-sol',reasoning='high',service='default',accepted_new=57,credit=0,protected_peers=['expanded-corpus-r497','expanded-corpus-r498'])
save(ROOT/'prime-like-goldbach-review-r1-ready.json',ready);save(ROOT/'selection-routing-prime-like-goldbach-review-r1.json',dict(ids=[368088],sources=[literal['source_url'],'https://arxiv.org/abs/2211.02865'],lane=str(R),task_sha256=ready['task_sha256'],metadata_only=True));save(ROOT/'r496-completion-boundary-delta.json',dict(utc=now,message=summary,new_protected_peer=R.name,immutable_worker_inputs_unchanged=True))
print(json.dumps(dict(files=132,frozen=13,bindings=20,receipts=len(receipts),guard_events=dict(counts),search_budget=budget,review=ready,credit=0,accepted_new=57)))
