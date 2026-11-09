"""Root documentary verification of r523 (zero survivors) and preparation of a focused three-target finite-statement lane; no root mathematics."""
import os,resource
os.sched_setaffinity(0,sorted(os.sched_getaffinity(0))[:2])
resource.setrlimit(resource.RLIMIT_CPU,(120,120))
resource.setrlimit(resource.RLIMIT_AS,(6*1024**3,6*1024**3))
from pathlib import Path
import json,hashlib,datetime,re,collections,ast,shutil
ROOT=Path(__file__).resolve().parent;P=ROOT.parent;chunks={}
t=ast.parse((ROOT/'intake-planar-review-r506-prepare-r508-r509.py').read_text());exec(compile(ast.Module(body=[x for x in t.body if isinstance(x,ast.FunctionDef)],type_ignores=[]),'<documentary-functions>','exec'),globals())
now=datetime.datetime.now(datetime.timezone.utc).isoformat();assert read(P/'ledger.json')['accepted_new']==57
A=P/'expanded-corpus-r523';L=P/'focused-finite-routes-sol-r1';assert not L.exists()

# Every documentary check precedes any root mutation.
m=read(A/'SEAL.json');assert len(m['files'])==195 and str(m['credit'])=='0' and m['accepted'] is False and m['frozen_count']==13 and m['frozen_mismatches']==[]
names=set()
for n,x in m['files'].items():
 assert not Path(n).is_absolute() and '..' not in Path(n).parts;names.add(n)
 q=A/n;assert not q.is_symlink() and sha(q)==x['sha256'] and q.stat().st_size==x['bytes'],n
aex=m['terminal_self_exclusions'];assert set(aex)=={'SEAL.json','seal.receipt.json','seal.output.txt'}
inventory=set()
for q in A.rglob('*'):
 assert not q.is_symlink()
 if q.is_file():inventory.add(str(q.relative_to(A)))
assert inventory==names|set(aex)
frozen(A,13);arec=receipts(A,{})
route=read(ROOT/'selection-routing-r523.json');assert sha(A/'TASK.txt')==route['task_sha256'] and sha(A/'reservation.json')==route['reservation_sha256']
ids=read(A/'reservation.json')['ids'];gates=read(A/'results.json');prov=read(A/'literal-provenance.json');assert len(ids)==len(prov)==len(gates)==20 and set(ids)==set(map(int,gates))==set(map(int,prov))
sources={};bound={}
for key,v in prov.items():
 raw,obj,token=corpus(dict(v,newline=v['raw_newline']));assert obj==v['object'] and obj['mathdb_id']==int(key)
 assert token.decode()==v['raw_statement_token'] and dg(token)==v['raw_statement_token_sha256'] and dg(obj['statement'].encode())==v['decoded_statement_utf8_sha256'];sources[key]=obj['source_url'];bound[key]=(raw,obj,v)
assert all(v['qualified_survivor'] is False for v in gates.values()) and not list(A.glob('FULLCANDIDATE*')) and not list(A.glob('DORMANT*'))
abudget=search(A,3,9,3,9,['search-response-1.txt','search-response-2.txt','search-response-3.txt'])
ae=guard(A,list(A.glob('get-*.json')),ids,dict(attempt=7,success=7),7)
hist=read(A/'history-access.json');allow=read(A/'historical-results-allowlist.json');names_h={x['path'] for x in hist};assert len(hist)==909 and len(allow)==910 and names_h<=set(allow) and len(set(allow)-names_h)==1
for x in hist:
 rel=Path(x['path']).relative_to(P);assert not any(t in part.lower() for part in rel.parts for t in ['formal','code-loop','code_loop','polynexus','crown','bunkbed','tournament','hat-bipartite'])
 assert not any(f'expanded-corpus-r{z}' in x['path'] for z in [395,463,466,482,524])
 if x.get('sha256'):assert allow[x['path']]==x['sha256'],x['path']

ass='r523 zero qualified survivors, no candidate, clean process record with no failed receipts. 348662: an exact integer partition-sum coefficient model is derived, with the common sign of the coefficients for every small star unproved; Lin-Pierson 2511.08665 covers large stars only. 364538: d at most 3 is source-known, parity and rounding are checked, and the all-d histogram realization is unpaid; the literal can be stated in finite terms. 358527: a cycle-domination bound chi<=2l+1 is proved but no uniform threshold; the literal is finite. 328744 is explicitly refuted in its own source note, zero. 326915 has a specifically identified Keusch public theorem, proof body unread. Sixteen assigned originals unread; recorded parks are not open-status certifications. Verified 195 manifest files, 20 corpus bindings, 13 frozen, 909 saved history entries, 7 GET successes (PDF), 3 searches / 9 strings with responses saved. No formal dispatch or credit.'
ar=dict(utc=now,source_lane=str(A),manifest_sha256=sha(A/'SEAL.json'),task_reservation_genesis_verified=True,verified_manifest_files=195,verified_frozen_bindings=13,verified_original_bindings=ids,source_url_by_id=sources,all20_gates=gates,runner_receipts=arec,guard_events=dict(collections.Counter(e['event'] for e in ae)),search_budget=abudget,verified_saved_history_names=909,scientific_summary=ass,root_disposition='ZERO_QUALIFIED_SURVIVORS_THREE_FINITE_ROUTES_FOCUSED',credit=0,accepted_new=57,terminal_self_exclusions=aex,root_scope='Documentary integrity only; no mathematical execution by root.')
den=read(ROOT/'inherited-denials-r551.json');den['utc']=now;den['root_r523_scope']=ass
save(P/'expanded-corpus-r523-parent-integration.json',ar);denpath=ROOT/'inherited-denials-r552.json';save(denpath,den)

L.mkdir();(L/'inputs').mkdir();(L/'inputs/sources').mkdir()
for h in ['bootstrap.py','run.py','write_lane.py','verify_frozen.py','registry-roots.json','source_get_guard.py','model-policy-sol-only.json','charge_search.py']:shutil.copyfile(A/h,L/h)
shutil.copyfile(denpath,L/'inherited-denials.json')
target=[348662,364538,358527];rows=[]
for tid in target:
 raw,obj,v=bound[str(tid)];(L/'inputs'/f'original{tid}.raw.jsonl').write_bytes(raw);save(L/'inputs'/f'literal{tid}.json',obj);save(L/'inputs'/f'provenance{tid}.json',v);save(L/'inputs'/f'r523-gates{tid}.json',gates[str(tid)]);rows.append(obj)
for f in ['SUSTAINED-ROUTES.md','ACTUALBRIEF.md','search-response-1.txt','search-response-2.txt','search-response-3.txt']:shutil.copyfile(A/f,L/'inputs'/f)
for f in ['star.pdf','star.txt','star-final.pdf','star-final.txt','star-followup.pdf','star-followup.txt','degree.pdf','degree.txt','local.pdf','local.txt']:shutil.copyfile(A/'sources'/f,L/'inputs/sources'/f)
shutil.copyfile(ROOT/'accepted57-review-context.json',L/'inputs/accepted57-scopes.json')
prior=P/'spherical-error-monotonicity-source-review-sol-r1/inputs/prior39-routing.json';assert sha(prior)=='6493e29137d286242b09d96f97dfe39a9ca5146a8d73bcfa8177e4705d6aaff3';shutil.copyfile(prior,L/'inputs/prior39-scopes.json')
save(L/'reservation.json',dict(ids=target,rows=rows,purpose='Focused sustained proof or counterexample attempts on three problems whose literal statements are finite'))
(L/'reservation.sha256').write_text(sha(L/'reservation.json')+'  reservation.json\n');save(L/'search-budget.json',dict(calls_used=0,queries_used=0,maximum_calls=3,maximum_queries=9,charged_before_call=True))
peers=['interval-kwidth-primary-qualification-sol-r2','expanded-corpus-r524']
task=f'''You are the sole worker: GPT-6.1 Sol HIGH reasoning, DEFAULT speed. No children, provider or model fallback, Lean, compiler, formal API, self-credit, git, install, publication, accounts, browser or external message. Root orchestrates; you do the mathematics. Campaign 57/60 beyond 39 prior, 96 total, unchanged.

FIRST shell command EXACTLY:
timeout 20 python3 -I -B {L}/bootstrap.py
SECOND shell command EXACTLY:
timeout 140 python3 -I -B {L}/verify_frozen.py before
No extra punctuation or chaining, and no reads or planning before those. Bootstrap and the standalone verifiers are explicit cap exceptions. Every other substantive local operation runs under the immutable ABSOLUTE {L}/run.py UNIQUE_LABEL with Python on stdin and an outer timeout 140. Authored writes go through the immutable ABSOLUTE {L}/write_lane.py. Do not edit frozen helpers, inputs, TASK or caps, and do not rerun bootstrap. Preserve true failures. An actual protected, frozen, access, guard, counter or cap breach means STOP and disclose, with no reset; an ordinary documentary failure is not automatically a breach.

Straight after the second command, read the COMPLETE TASK.txt and the COMPLETE inherited-denials.json in contiguous capped runner chunks of at most 15000 characters, recording the ranges. Every identified failed work in inherited-denials.json is closed to all new deliveries by any route.

SCOPE. Exactly three targets, fixed in reservation.json, chosen because their literal statements can be written in finite terms and earlier work left concrete partial routes. Unlike a twenty-problem screening round, you have the whole session for these three. Spend it on sustained mathematics. Read inputs/SUSTAINED-ROUTES.md and the source passages, then push each route as far as it will go, in order of what you judge most tractable after your first reading.

1. MathDB 348662, star-target p-monotonicity for H-chromatic symmetric functions, 2011.06063 Conjecture 9.6 and its final form. Lin-Pierson 2511.08665 covers large stars only. The partial route is the exact integer coefficient model S_lambda over set partitions into independent blocks with quotient injective homomorphisms. Decide whether S_lambda has a common sign for every lambda at every finite n, through a sign-reversing involution or a direct orientation argument, or find a small explicit graph and star for which two coefficients have opposite signs. An explicit counterexample computed by hand would be the ideal outcome.
2. MathDB 364538, sharp degree balance in regular graphs, 2408.16121v2 Conjecture 3.2. d at most 3 is known, and the source says it cannot adapt its induction to d>=4. The partial routes are alternating-trail improvement moves and disjoint-union obstructions. Either give a real all-d proof, or construct an explicit persistent obstruction beyond the handshaking parity, which would need infinitely many non-exceptional graphs for some fixed d.
3. MathDB 358527, a cycle in some tournament out-neighbourhood, 2305.15585 Conjecture 11. The proved helper is chi<=2l+1 for a cycle of length l in G when all out-neighbourhood graphs are forests. Either find a structural dichotomy giving a uniform chromatic bound, or build a chromatic-raising construction preserving the local-forest constraints.
Be honest about difficulty. These are open problems and a precise statement of why a route fails is a good outcome. Do not pad; do not claim progress you do not have.

SIGNIFICANCE AND LEAN. Recent proposals in this campaign were correct but excluded as routine: applying a source's own sufficient theorem, changing one estimate in a source's proof, extending an exact count for a closely related model, or proving a special case of a statement a classical criterion settles in general form. Check for these early. Every accepted result needs a literal kernel-checked Lean endpoint, and Lean modules importing real analysis, measure theory, linear algebra, fields or ring tactics currently fail their kernel checks here, so keep each statement and proof in natural numbers, finite sets, finite graphs and finite words wherever possible, and say so explicitly.

NO COMPUTATION. No mathematical programs, enumeration, numerical experiments, CAS or solver. Hand calculation only. Hash, source and PDF processing is permitted under the runner.

ACCESS. Active peers {peers[0]} and {peers[1]} are entirely protected, including metadata, stat, read, hash, list, glob, poll and reservations. All formal, code-loop, Polynexus, crown, bunkbed, tournament and Hat campaign bodies and integrations are protected. Access only your own lane and the explicit PDF skill at /home/mj-kang/.codex/plugins/cache/openai-primary-runtime/pdf/26.1103.10131/skills/pdf/SKILL.md, announcing it if used. Embedded provenance paths are no permission to follow them.

NETWORK. Budget at most 6 guarded GET hops, 3 native searches and 9 exact query strings. The sole GET client is the immutable ABSOLUTE {L}/source_get_guard.py under your runner, one manually chosen persisted exact plan per invocation with fields url, routes, destination, source_identity and purpose, routes being reserved ID strings. No guessed URL, batching, Citeseer, Wayback, /server/api/, custom HTTP, curl, wget or browser. A denial, challenge or redirect to a blocked route closes that work and stops your network use, so prefer direct arXiv or open PDF URLs you actually observed. Before each native search, persist the exact query plan through the writer and precharge the counter with the immutable ABSOLUTE {L}/charge_search.py under your runner. In the very next tool call after each search returns, before any thinking, reading or other step, save the COMPLETE response text into the lane through the writer. If the first save fails, recover from the same stored response and never re-search. Search results are navigation only.

PRIOR ART. If you reach a full proof or refutation of a target, before claiming it check the actual literature for it, read the applicable primary bodies you can reach, and record the strongest case on each side. A bounded nonmatch is not a worldwide novelty claim.

CAPS. Affinity<=2, child CPU 115, supervisor 120, AS 6GiB, sampled group RSS 6GiB, deadline 130, outer timeout 140. All jobs synchronous and reaped. Preserve every failed attempt with its true exit. No universal process, cgroup or peak claims.

DELIVERABLES. results.json with one entry per target ID and separate literal, source, ordinary, prior, novelty, significance, formal, independent and acceptance gates, plus disposition, qualified_survivor and credit fields. ROUTES.md with what you actually proved, every failed mechanism and the exact unpaid lemma for each target. For any full proof or refutation, FULLCANDIDATE-<id>.md and DORMANT-SOL-FORMAL-PLAN-<id>.md, with no dispatch. ACTUALBRIEF.md as the handback. Then run the standalone verify_frozen.py after, THEN seal an exhaustive own-lane byte manifest MANIFEST.json, naming precisely the terminal noncircular self-exclusions. No later frozen writes. Credit 0, 57/60 unchanged. Root alone adjudicates. Stop at handback.
'''
(L/'TASK.txt').write_text(task);ff=[q for q in L.iterdir() if q.is_file() and q.name!='search-budget.json']+[q for q in (L/'inputs').rglob('*') if q.is_file()];save(L/'frozen-inputs.json',{str(q):sha(q) for q in ff})
ready=dict(utc=now,lane=str(L),ids=target,task_sha256=sha(L/'TASK.txt'),frozen_bindings=len(ff),model='gpt-6.1-sol',reasoning='high',service='default',accepted_new=57,credit=0,protected_peers=peers,latest_denials=str(denpath))
save(ROOT/'focused-finite-routes-r1-ready.json',ready);save(ROOT/'selection-routing-focused-finite-routes-r1.json',dict(ids=target,sources=[o['source_url'] for o in rows],lane=str(L),task_sha256=ready['task_sha256'],metadata_only=True))
print(json.dumps(dict(r523_manifest=195,frozen=13,corpus=20,history=909,focused=ready,credit=0,accepted_new=57)))
