"""Root documentary integrity and disjoint metadata-only selection; no mathematics."""
import os,resource
os.sched_setaffinity(0,sorted(os.sched_getaffinity(0))[:2]);resource.setrlimit(resource.RLIMIT_CPU,(120,120));resource.setrlimit(resource.RLIMIT_AS,(6*1024**3,6*1024**3))
from pathlib import Path
import json,hashlib,datetime,collections,re,importlib.util
P=Path(__file__).resolve().parent.parent;ROOT=P/'root-intake-r60';A=P/'expanded-corpus-r493'
def sha(q):return hashlib.sha256(q.read_bytes()).hexdigest()
def dg(b):return hashlib.sha256(b).hexdigest()
def read(q):return json.loads(q.read_text())
def save(q,d):
 assert not q.exists(),str(q)
 q.write_text(json.dumps(d,indent=2)+'\n')
now=datetime.datetime.now(datetime.timezone.utc).isoformat();assert read(P/'ledger.json')['accepted_new']==57
route=read(ROOT/'selection-routing-r493.json');assert sha(A/'TASK.txt')==route['task_sha256'] and sha(A/'reservation.json')==route['reservation_sha256']
m=read(A/'MANIFEST.sha256.json');entries=m['files'];assert len(entries)==115
for n,v in entries.items():
 assert not Path(n).is_absolute() and '..' not in Path(n).parts
 q=A/n;assert not q.is_symlink() and sha(q)==v['sha256'] and q.stat().st_size==v['bytes'],n
ex=m['exclusions'];assert set(ex)=={'MANIFEST.sha256.json','terminal_manifest.receipt.json','terminal_manifest.output.txt'}
actual=set()
for q in A.rglob('*'):
 assert not q.is_symlink()
 if q.is_file():actual.add(str(q.relative_to(A)))
assert actual==set(entries)|set(ex)
frozen=read(A/'frozen-inputs.json');assert len(frozen)==13 and all(Path(n).parent==A and sha(Path(n))==h for n,h in frozen.items())
after=read(A/'frozen-after.json');before=read(A/'frozen-before.json');assert before['count']==after['count']==13 and before['mismatches']==after['mismatches']==[]
gates=read(A/'results.json');prov=read(A/'original-provenance.json');ids=read(A/'reservation.json')['ids'];assert len(ids)==len(prov)==20 and set(ids)==set(map(int,gates))=={r['id'] for r in prov}
chunks={};sources={}
for row in prov:
 key=str(row['id']);q=Path(row['chunk']);assert q.is_relative_to(P.parent/'lanes/pi-mathdb-full-corpus-inventory-r301/corpus')
 if str(q) not in chunks:
  b=q.read_bytes();chunks[str(q)]=(dg(b),b.splitlines(keepends=True))
 h,lines=chunks[str(q)];assert h==row['chunk_sha256'];raw=lines[row['line']-1];obj=json.loads(raw)
 assert row['newline'] is True and raw.endswith(b'\n') and dg(raw)==row['raw_sha256'] and (A/'originals'/f'{key}.jsonl').read_bytes()==raw and obj['mathdb_id']==row['id']
 tokens=re.findall(rb'"statement"\s*:\s*("(?:[^"\\]|\\.)*")',raw);assert len(tokens)==1;token=tokens[0]
 assert token.decode()==row['raw_statement_token'] and dg(token)==row['token_sha256'] and json.loads(token)==obj['statement']==gates[key]['literal_statement']==row['decoded_statement'] and dg(obj['statement'].encode())==row['decoded_sha256'];sources[key]=obj['source_url']
receipts=[]
for q in sorted(A.glob('*.receipt.json')):
 v=read(q);assert v['cwd']==str(A) and v['cpu_limit_s']==115 and v['as_limit_bytes']==6*1024**3 and v['group_rss_guard_bytes']==6*1024**3 and v['deadline_s']==130 and len(v['affinity'])<=2 and v['killed'] is None
 receipts.append(dict(path=q.name,sha256=sha(q),exit=v['exit']))
assert read(A/'terminal_manifest.receipt.json')['exit']==0
budget=read(A/'search-budget.json');assert budget==dict(calls_used=2,queries_used=6,maximum_calls=3,maximum_queries=9,charged_before_call=True)
charges=[json.loads(s) for s in (A/'search-charges.jsonl').read_text().splitlines()];assert len(charges)==2
prev=dict(calls_used=0,queries_used=0,maximum_calls=3,maximum_queries=9,charged_before_call=True)
for i,c in enumerate(charges,1):
 assert c['sequence']==i and c['before']==prev and sha(A/c['plan'])==c['plan_sha256'] and read(A/c['plan'])['queries']==c['queries']
 nxt=dict(prev,calls_used=i,queries_used=prev['queries_used']+len(c['queries']));assert c['after']==nxt;prev=nxt
 response=(A/('search-one-response.json' if i==1 else 'search-two-response.json')).read_text();assert len(response)>1000
assert prev==budget and sha(A/'charge_search.py')==sha(ROOT/'charge_search.py')
events=[];prev='0'*64
plans={dg(json.dumps(read(q),sort_keys=True).encode()):read(q) for q in [q for q in (A/'plans').glob('*.json') if not q.name.startswith('search-')]}
for i,line in enumerate((A/'guard-ledger.jsonl').read_bytes().splitlines(keepends=True)):
 e=json.loads(line);assert e['seq']==i and e['previous']==prev;prev=dg(line);events.append(e)
 if e['event']=='success':
  q=A/e['destination'];assert sha(q)==e['sha256'] and q.stat().st_size==e['bytes']
 if e['event']=='attempt':assert e['plan_sha256'] in plans and '/server/api/' not in e['url'] and e['url'].startswith('https://') and set(e['routes'])<=set(map(str,ids))
counts=collections.Counter(e['event'] for e in events);assert counts==dict(attempt=5,success=4,redirect=1)
history=read(A/'history-access.json');allow=read(A/'historical-results-allowlist.json');assert len(history)==831
forbidden=('formal','code-loop','code_loop','polynexus','crown','bunkbed','tournament','hat-bipartite')
for x in history:
 rel=Path(x['path']).relative_to(P)
 assert not any(t in part.lower() for part in rel.parts for t in forbidden)
 assert not any(f'expanded-corpus-r{n}' in x['path'] for n in [395,463,466,482]) and x['path'] in allow and allow[x['path']]==x['sha256']
assert events[-1]['location']=='http://ieeexplore.ieee.org/document/6094262/' and read(A/'get_tree_final.receipt.json')['exit']==1
assert 'Only explicit credential-free HTTPS URLs are allowed' in (A/'get_tree_final.output.txt').read_text()
successes=[e for e in events if e['event']=='success'];assert sum((A/e['destination']).read_bytes().startswith(b'%PDF') for e in successes)==3
summary='317672 author full universal quarter-radius upper-bound proposal: two explicit rooted logical trees with all internal degrees>=3, same minedge1, different topology, terminal metric separation1/2; midpoint error1/4 forces arbitrary algorithm contradiction for every radius>1/4 even with known minedge. All path classes/strictness paid by author, NOT independent ordinary PASS. Actual source RNJ lower guarantee attributed; full literal consequent/source/prior/significance/independent/formal HOLD. Earlier Computational Problems in Evolution thesis body unread.322031 Tutte active-row/lower-base-roof reductions leave full low-dimensional face classification/counts unpaid.320730 tomography low-defect helpers leave simultaneous switch/Pareto/border induction unpaid. Seventeen originals unread.115 files20 raw/token/decoded bindings13 frozen831 saved historical names verified;5 HTTPS GET attempts4 payloads3PDF1metadata1blockedHTTPredirect,2 searches6queries. Guard STOP/nonPASS and logger failure retained, no actual prohibited HTTP fetch.'
record=dict(utc=now,source_lane=str(A),task_reservation_genesis_verified=True,manifest_sha256=sha(A/'MANIFEST.sha256.json'),verified_manifest_files=115,verified_original_bindings=ids,verified_frozen_bindings=13,source_url_by_id=sources,all20_gates=gates,runner_receipts=receipts,guard_events=dict(counts),search_budget=budget,root_disposition='ZERO_QUALIFIED_SURVIVORS_317672_ASSIGNED_INDEPENDENT_REVIEW',scientific_summary=summary,process='Exact own manifest, corpus bindings, frozen inputs and831 saved allowlisted names verified; root did not follow external history paths. Late search/guard source failure preserved, no invented unavailable row/HTTP request/retry/HTTPS upgrade. Material read-depth and native/transient/writer telemetry limits retained; no universal process or source-body PASS.',credit=0,accepted_new=57,target_new=60,formal_dispatch=False,terminal_self_exclusions=ex,root_scope='Documentary integrity/routing only, no root mathematical solving/programs/Lean/checkers.')
den=read(ROOT/'inherited-denials-r503.json');den['utc']=now;den['root_r493_scope']=summary
den['blocked_keys']=sorted(set(den['blocked_keys'])|{'doi.org/10.1109/TIT.2011.2168901','ieeexplore.ieee.org/document/6094262/'})
den['blocked_artifacts']=sorted(set(den['blocked_artifacts'])|{'0809.0158','10.1109/tit.2011.2168901','6094262','network tomography based on additive metrics'})
restriction='ENTIRE identified Ni-Tatikonda Network Tomography Based on Additive Metrics original0809.0158/finalIEEE2011 DOI10.1109/TIT.2011.2168901 document6094262 ALL NEW hosts,versions,arxiv,authors,caches,mirrors,DOI/API,body/metadata deliveries unavailable. HTTPS DOI302 to HTTP target guard-rejected BEFORE dispatch; error logger also failed. No retry/HTTPS upgrade/alternate identity/indirect recovery. Explicit pre-denial original/metadata only, not final equivalence. Distinct actual prior thesis is not itself denied.'
den['records'].append(dict(url='https://doi.org/10.1109/TIT.2011.2168901',reason=dict(status='HTTP redirect guard rejection before dispatch, logger failed',artifact='Ni-Tatikonda Network Tomography Based on Additive Metrics',restriction=restriction),evidence=dict(path=str(A/'get_tree_final.receipt.json'),sha256=sha(A/'get_tree_final.receipt.json'),guard_sha256=sha(A/'guard-ledger.jsonl'))))
delta=summary+' NEW '+restriction;denpath=ROOT/'inherited-denials-r504.json'
# All integrity assertions precede integration and new review preparation.
save(P/'expanded-corpus-r493-parent-integration.json',record);save(denpath,den)
import shutil
R=P/'tree-reconstruction-radius-source-review-sol-r1';assert not R.exists();R.mkdir();(R/'inputs').mkdir()
for name in ['bootstrap.py','run.py','write_lane.py','verify_frozen.py','registry-roots.json','source_get_guard.py','model-policy-sol-only.json','charge_search.py']:shutil.copyfile(A/name,R/name)
shutil.copyfile(denpath,R/'inherited-denials.json')
literal=json.loads((A/'originals/317672.jsonl').read_text());prow=next(r for r in prov if r['id']==317672)
shutil.copyfile(A/'originals/317672.jsonl',R/'inputs/original317672.raw.jsonl');save(R/'inputs/provenance317672.json',prow);save(R/'inputs/literal317672.json',literal);save(R/'inputs/author-gates317672.json',gates['317672'])
for name in ['FULLCANDIDATE.md','DORMANT-SOL-FORMAL-PLAN.md','NETWORK-STOP.md','read-inventory.json','search-one-response.json','search-two-response.json']:shutil.copyfile(A/name,R/'inputs'/name)
for name in ['tree.pdf','tree.txt','tree-metadata.html']:shutil.copyfile(A/'sources'/name,R/'inputs'/name)
for name in ['tree.json','tree-final.json','tree-metadata.json']:shutil.copyfile(A/'plans'/name,R/'inputs'/('author-plan-'+name))
shutil.copyfile(ROOT/'accepted57-review-context.json',R/'inputs/accepted57-scopes.json');prior=P/'spherical-error-monotonicity-source-review-sol-r1/inputs/prior39-routing.json';assert sha(prior)=='6493e29137d286242b09d96f97dfe39a9ca5146a8d73bcfa8177e4705d6aaff3';shutil.copyfile(prior,R/'inputs/prior39-scopes.json')
save(R/'reservation.json',dict(ids=[317672],rows=[literal],purpose='Independent full literal general-tree distance-reconstruction quarter-radius impossibility, exact source conventions, primary prior/significance review; no formal tools'))
(R/'reservation.sha256').write_text(sha(R/'reservation.json')+'  reservation.json\n');save(R/'search-budget.json',dict(calls_used=0,queries_used=0,maximum_calls=2,maximum_queries=6,charged_before_call=True))
task=f'''Use ONLY GPT-6.1 Sol, high effort, default speed. Personally perform independent full ordinary-proof, literal/source and significance review for MathDB317672. No children, fallback, mathematical programs, enumeration, numerical experiments, CAS/solver, Lean/compiler/checker/formal API or self-credit. Root orchestrates; you do mathematics/source qualification. Current57/60 beyond39 prior,96 total. Complete bounded investigation, not acquisition-only. No formal dispatch.

FIRST shell command EXACTLY:
timeout 20 python3 -I -B {R}/bootstrap.py
Read COMPLETE printed TASK/AGENTS. SECOND shell command EXACTLY:
timeout 140 python3 -I -B {R}/verify_frozen.py before
No punctuation/chaining. Bootstrap and standalone verifiers are explicit cap exceptions. Every other substantive local shell/document/source/PDF operation immutable ABSOLUTE {R}/run.py UNIQUE_LABEL Python stdin with timeout140. Authored writes immutable ABSOLUTE {R}/write_lane.py. Never edit frozen helpers/inputs/TASK/caps or rerun bootstrap. Fresh diagnostic repair allowed; preserve all failures. Actual protected/frozen/access/guard/counter/cap breach STOP/quarantine without reset; documentary typo/render/serialization failure is not automatically a breach.

SOLE317672. Protected active peers expanded-corpus-r494 and expanded-corpus-r495 entirely, including metadata/stat/read/hash/list/glob/poll/reservations/flat integrations. Own inputs/products and explicit PDF skill ONLY, no author/ROOT/campaign/sibling/history/embedded-path access. No historical allowlist here. All formal/code-loop/Polynexus/crown/bunkbed/tournament/Hat bodies and flat integrations protected. ENTIRE r395/r463/r466/r482 packets permanently quarantined, no use/refetch seeds. No shared/parent/tmp writes, git, installs, publication, external messages, accounts or browser. Trusted supplied57+39 scopes only, no upstream truth/certificate audit.

Read raw/literal first. Actual endpoint says NO distance-based algorithm has l-infinity radius greater than1/4 for GENERAL trees, with a consequent that RNJ Algorithm3 is optimal given min edge Delta and its preceding lower guarantee. Independently reconstruct the whole ordinary obstruction BEFORE opening FULLCANDIDATE.md, then adversarially audit it. Mechanism is disclosed in this task, so independent verification/reconstruction is not independent invention. Source cached0809.0158 v1 actual Section2 pp4–6 logical tree/root/terminal conventions, Definition4 p14 strict noisy-input radius, Algorithm3 pp20–21, Lemma2/Proposition6/Corollary1 p22 and Conjecture1/Proposition7 p23, ALL relevant proof/hypotheses must be personally read. Review exact source root as terminal/internal? source observed terminal set? binary/nonbinary/degree2 suppression, edge positivity, minimum side information, labelled root and estimated metric/additivity restrictions, deterministic/randomized guarantee and quantification. Do not replace the target by a table-only problem or threshold algorithms. Pay literal RNJ-optimal consequent with the actual lower-bound theorem/proof and precise dependence on supplied Delta, not an unread attribution or new axiom. Any eventual formal plan must include full lower-bound/Algorithm3 bridges if required by literal, even if ordinary new contribution is upper-bound only.

Author construction to verify after your independent reconstruction: U={{s,z,a,b,c}}, root s. T0 internal u,v, edges su,zu length1; uv,va,vb,vc length5/4. T1 internal u,v,w, all edges su,zu,uv,va,vw,wb,wc length1. Each is actually connected/acyclic with terminal leaves/internal undirected degree>=3; source rooted orientation away from s gives each internal at least2 children if conventions match. Minima both1, unlike the preliminary four-terminal star/resolved quartet whose minima differ. Degree multisets differ, hence nonisomorphic even before terminal labels. Pay graph/tree/metric bridges, not merely declared path table.

Author claimed distance table: sz2/2; sa,za7/2 versus3; sb,sc,zb,zc7/2 versus4; ab,ac5/2 versus3; bc5/2 versus2. Verify EVERY unordered pair and exhaustion/symmetric diagonal, genuine midpoint metric if input requires it, sup separation exactly1/2 and midpoint error1/4. Identical labels/root/minimum side information force ANY algorithm on common midpoint to output two incompatible topologies under radius r>1/4; strict inequality is essential and no failure at exact strict radius1/4 is claimed. Cover all r, scale Delta>0 if source requires, input minima known/unknown, same terminal data and every admissible algorithm. Randomized certainty versus weaker probability guarantees must not be conflated. Explain why no contradiction with binary radius1/2 (T0 has degree4). If source domain requires something different, repair concretely or precise GAP; source/domain correction is zero-credit, not silently widened theorem.

Use/announce/read PDF skill /home/mj-kang/.codex/plugins/cache/openai-primary-runtime/pdf/26.1103.10131/skills/pdf/SKILL.md. Visually inspect material actual Definition4/Conjecture1/degree-root/input/minimum glyphs and any needed figure, not text extraction alone. Read-only native presentation of PERMITTED own rendered PDF pages is explicitly allowed outside runner; image creation/conversion/processing under runner, no filesystem code outside caps, native/transient/writer/supervisor peaks unknown. No PDF authoring or installs.

Scientific qualification: actual original conjecture is UNIVERSAL but Proposition7 only treats a threshold-neighbor algorithm class; reconstruct that exact difference and full source proof before adopting it. Strong positive case: removes algorithm restriction and equal-known-minimum repair pays side information, resolves full published conjecture, not parameter/domain correction; small witness/shortness alone does not make routine. Strong contrary case: a complete known general-tree metric indistinguishability/edge-radius theorem or exact final resolution may subsume the construction; ordinary quarter-radius star/quartet adaptation may be routine if FULL source-to-target proof bridge supplied. Read actual prior theorem and proof, all tree/output/side-information hypotheses, then demonstrate complete reduction before excluding. Do not infer public/routine exclusion from abstract, source citations, standard-tool names, shortness or open labels.

Specific unread lead from actual saved searches: Computational Problems in Evolution, observed https://www.diva-portal.org/smash/get/diva2%3A11046/FULLTEXT01.pdf , discussion of optimal reconstruction radius/edge radius. Authenticate author/date/title from actual primary body, inspect full applicable proof/standing hypotheses; no invented theorem identity. Atteson binary-tree1/2 is source-attributed, not already a complete nonbinary1/4 bridge. Distinct prior bodies are not blanket denied. Specific applicable unread proof remains HOLD; generic worldwide unknown is not automatic veto, bounded nonmatches not novelty. Compare57+39 exact supplied scopes, one family all tree/Delta/root/algorithm/helper variants; no certificate audit.

ENTIRE ORIGINAL/FINAL CLOSED: Ni-Tatikonda Network Tomography Based on Additive Metrics original0809.0158/final IEEE2011 DOI10.1109/TIT.2011.2168901 document6094262. DOI HTTPS302 to HTTP IEEE target was guard-rejected BEFORE dispatch; logger also failed. No new original/final body OR METADATA/query/hosts/versions/arxiv/authors/caches/mirrors/DOI/API/indirect recovery/HTTPS upgrade/retry. Explicit supplied pre-denial v1 and metadata only, NOT final equivalence/correction absence. This does NOT deny distinct prior thesis. Prior author STOP/nonPASS remains preserved, not reset by this fresh independent task; you are authorized only copied pre-stop inputs plus distinct lawful primary comparisons. Keep final-source HOLD explicit if unread; no final-equivalence from thesis or abstract. Four public registry ROOT artifacts unavailable, no README/tree/API/branch/mirror refresh/reconstruction.

Network: read COMPLETE inherited-denials before requests, recover truncations. Sole GET immutable ABSOLUTE source_get_guard.py UNDER run.py; ONE persisted manually chosen exact plan/invocation, routes['317672'], NEW own sources destination, actual observed URL, source_identity/purpose>=12chars. Max6 GET HOPS including redirects, max2 native SEARCH calls/6 exact query strings for this separate review; no unused author-lane budget reset/resume. Before EACH search persist queries-list plan through writer, read LIVE counter/ledger, precharge immutable ABSOLUTE charge_search.py under runner. Save FULL actual response immediately before further work as ordinary JSON/string, no btoa/TextEncoder; local serialization error may recover SAME in-memory response without new call. No counter resets/refunds/manual edits. No API including /server/api/ bitstreams, custom transport/curl/wget/requests/HEAD/native URLopen/browser/POST/TLS/cookie/JS/meta-refresh workarounds. Failure of identified work closes ALL NEW deliveries across hosts/versions/arxiv/authors/cache/mirror/DOI/API/body/metadata, no alternate identity/indirect recovery. Guard rejection STOP, preserve exact ledger and true exit; no unavailable-row backfill. Transport200 nonpaper not primary-body PASS. No network after an actual stop.

Caps affinity<=2,childCPU115/supervisor120,AS6GiB,sampled groupRSS6GiB,deadline130/outer140,arena2. Standalone verifierCPU120 exception not nested under child115. All runner receipts true exits/resources/synchronous reap, no background jobs. No universal cgroup/process-cap assertion from sampled RSS or unknown native peaks.

Deliver REVIEW.md, independent PROOF.md or precise GAP.md, keyed review.json317672 with separate literal/source/ordinary/prior/novelty/significance/family/formal/independent/procedure/acceptance gates, strongest opposing cases and complete prior bridges, source map, read/visual/access/search/resource inventories and receipts. Conditional updated dormant Sol formal plan ONLY if ordinary full literal and substantive scientific gates prospectively survive; include actual weighted rooted trees/paths, nonisomorphism, arbitrary algorithms/strict radius, RNJ lower guarantee bridges, audits/replay/paper dependencies, not implementation/dispatch. Final standalone verify_frozen.py after THEN exhaustive manifest EVERY own file/helpers/frozen inputs/plans/payloads/full responses/ledgers/ALL completed receipt JSON, exact terminal noncircular exclusions, no later frozen writes. Complete bounded review or exact gaps; credit0,accepted57/60 unchanged pending root acceptance.
'''
(R/'TASK.txt').write_text(task);ff=[q for q in R.iterdir() if q.is_file() and q.name!='search-budget.json']+list((R/'inputs').iterdir());save(R/'frozen-inputs.json',{str(q):sha(q) for q in ff})
ready=dict(utc=now,lane=str(R),mathdb_id=317672,task_sha256=sha(R/'TASK.txt'),frozen_bindings=len(ff),model='gpt-6.1-sol',reasoning='high',service='default',accepted_new=57,credit=0,protected_peers=['expanded-corpus-r494','expanded-corpus-r495'])
save(ROOT/'tree-reconstruction-radius-review-r1-ready.json',ready);save(ROOT/'selection-routing-tree-reconstruction-radius-review-r1.json',dict(ids=[317672],sources=[literal['source_url']],lane=str(R),task_sha256=ready['task_sha256'],metadata_only=True))
save(ROOT/'r493-completion-boundary-delta.json',dict(utc=now,message=delta,new_protected_peer=R.name,immutable_worker_inputs_unchanged=True))
print(json.dumps(dict(files=115,frozen=13,bindings=20,receipts=len(receipts),guard_events=dict(counts),search_budget=budget,review=ready,credit=0,accepted_new=57)))
