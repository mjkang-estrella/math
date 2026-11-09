"""Root documentary verification, stopped-source propagation, disjoint metadata selection."""
import os,resource
os.sched_setaffinity(0,sorted(os.sched_getaffinity(0))[:2]);resource.setrlimit(resource.RLIMIT_CPU,(120,120));resource.setrlimit(resource.RLIMIT_AS,(6*1024**3,6*1024**3))
from pathlib import Path
import json,hashlib,datetime,collections,importlib.util
P=Path(__file__).resolve().parent.parent;ROOT=P/'root-intake-r60';A=P/'tree-reconstruction-radius-source-review-sol-r1'
def read(p):return json.loads(p.read_text())
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def dg(b):return hashlib.sha256(b).hexdigest()
def save(p,d):
 assert not p.exists(),str(p)
 p.write_text(json.dumps(d,indent=2)+'\n')
now=datetime.datetime.now(datetime.timezone.utc).isoformat();assert read(P/'ledger.json')['accepted_new']==57
ready=read(ROOT/'tree-reconstruction-radius-review-r1-ready.json');assert sha(A/'TASK.txt')==ready['task_sha256']
m=read(A/'MANIFEST.json');entries={v['path']:v for v in m['files']};assert len(entries)==len(m['files'])==105
for n,v in entries.items():
 assert not Path(n).is_absolute() and '..' not in Path(n).parts
 q=A/n;assert not q.is_symlink() and sha(q)==v['sha256'] and q.stat().st_size==v['bytes'],n
ex=m['exact_terminal_exclusions'];assert set(ex)=={'MANIFEST.json','terminal_manifest.receipt.json','terminal_manifest.output.txt'}
actual=set()
for q in A.rglob('*'):
 assert not q.is_symlink()
 if q.is_file():actual.add(str(q.relative_to(A)))
assert actual==set(entries)|set(ex)
fr=read(A/'frozen-inputs.json');assert len(fr)==30
for n,h in fr.items():assert Path(n).is_relative_to(A) and sha(Path(n))==h
for n in ['frozen-before.json','frozen-after.json']:
 v=read(A/n);assert v['count']==30 and v['mismatches']==[]
literal=read(A/'inputs/literal317672.json');assert json.loads((A/'inputs/original317672.raw.jsonl').read_text())==literal and literal['mathdb_id']==317672
receipts=[]
for q in sorted(A.glob('*.receipt.json')):
 v=read(q);assert v['cwd']==str(A) and v['cpu_limit_s']==115 and v['as_limit_bytes']==6*1024**3 and v['group_rss_guard_bytes']==6*1024**3 and v['deadline_s']==130 and len(v['affinity'])<=2 and v['killed'] is None
 receipts.append(dict(path=q.name,sha256=sha(q),exit=v['exit']))
assert read(A/'terminal_manifest.receipt.json')['exit']==0 and read(A/'get_fastnj.receipt.json')['exit']==1
budget=read(A/'search-budget.json');assert budget==dict(calls_used=1,queries_used=3,maximum_calls=2,maximum_queries=6,charged_before_call=True)
charges=[json.loads(s) for s in (A/'search-charges.jsonl').read_text().splitlines()];assert len(charges)==1;c=charges[0]
assert c['sequence']==1 and c['before']==dict(budget,calls_used=0,queries_used=0) and c['after']==budget and len(c['queries'])==3
assert sha(A/c['plan'])==c['plan_sha256'] and read(A/c['plan'])['queries']==c['queries'] and sha(A/'charge_search.py')==sha(ROOT/'charge_search.py')
response=read(A/'search-one-full-response.json');assert isinstance(response,(str,dict,list)) and len(json.dumps(response))>1000
plans={dg(json.dumps(read(q),sort_keys=True).encode()):read(q) for q in A.glob('get-*-plan.json')};events=[];previous='0'*64
for i,line in enumerate((A/'guard-ledger.jsonl').read_bytes().splitlines(keepends=True)):
 e=json.loads(line);assert e['seq']==i and e['previous']==previous;previous=dg(line);events.append(e)
 if e['event']=='attempt':assert e['plan_sha256'] in plans and e['routes']==['317672'] and e['url'].startswith('https://') and '/server/api/' not in e['url']
 if e['event']=='success':
  q=A/e['destination'];assert sha(q)==e['sha256'] and q.stat().st_size==e['bytes'] and q.read_bytes().startswith(b'%PDF')
counts=collections.Counter(e['event'] for e in events);assert counts==dict(attempt=2,success=1,redirect=1,unavailable=1)
failure=events[-1];assert failure['event']=='unavailable' and failure['error']=="PolicyError('Inherited/current unavailable route or artifact: no retry')"
assert failure['url']==events[-2]['location'] and not any(e['event']=='attempt' and e['url']==failure['url'] for e in events)
assert not (A/'sources/fast-neighbor-joining.pdf').exists()
review=read(A/'review.json');assert review['317672']['acceptance']['credit']==0 and review['317672']['family']['status']=='HOLD_INCOMPLETE_PERSONAL_COMPARISON'
summary='317672 independent pre-stop ordinary reconstruction supports FULL cached-v1 literal including actual RNJ lower guarantee via completed LCA/convex-score induction, not an assumption that synthetic distances preserve original errors. Two actual trees/equal minimum/all10 paths/midpoint metric/nonisomorphism/all algorithms/strict radius/scaling verified by reviewer before candidate read; disclosed mechanism not independent invention. Source required pages visually read. Final original0809.0158/IEEE2011 remains closed/unread. Elias2006 thesis discussion read, detailed cited FNJ/Atteson proofs unread, binary half-radius/edge-recovery discussion not complete nonbinary quarter-radius subsumer. Actual FNJ request redirected to inherited blocked Wayback route, rejected BEFORE redirected dispatch;2 actual GET hops1thesisPDF1redirect1unavailable,trueexit1. No logger failure here, no redirected body fetched/retry/reset. Full57+39 family comparison remains unpaid due truncations; prior/significance/novelty HOLD.105 own files30 frozen verified,1 search3 strings. Root retains pre-stop ordinary evidence as held, no technical/acceptance PASS, no formal dispatch/credit;57/60 unchanged.'
restriction='ENTIRE identified Elias-Lagergren Fast Neighbor Joining, ICALP2005 LNCS3580 pp1263-1274, Citeseer document doi fc80df4469c8556fed45357cea8ba65f0c97535e ALL NEW hosts/versions/arxiv/authors/caches/mirrors/DOI/API/body/METADATA deliveries unavailable after automatic redirect guard rejection. No retry/alternate identity/indirect recovery. Blocked redirected Wayback request NEVER dispatched. Distinct already acquired Elias Computational Problems in Evolution thesis is not itself denied and is not an acquired FNJ paper/proof.'
record=dict(utc=now,source_lane=str(A),task_genesis_verified=True,manifest_sha256=sha(A/'MANIFEST.json'),verified_manifest_files=105,verified_frozen_bindings=30,runner_receipts=receipts,receipt_exit_counts=dict(collections.Counter(str(x['exit']) for x in receipts)),guard_events=dict(counts),search_budget=budget,review=review,root_disposition='SCIENTIFIC_PARK_PRESTOP_FULL_ORDINARY_EVIDENCE_RETAINED',scientific_summary=summary,procedure='STOP/nonPASS quarantine retained; no prohibited redirected fetch observed and no inherited blocked-work retry dispatched. Frozen integrity does not cure STOP. Native/transient/writer/supervisor resource limits and incomplete personal family comparison retained. No root mathematical solving or certificate acceptance.',credit=0,accepted_new=57,formal_dispatch=False,terminal_self_exclusions=ex)
den=read(ROOT/'inherited-denials-r506.json');den['utc']=now;den['root_tree_radius317672_review_scope']=summary
den['blocked_keys']=sorted(set(den['blocked_keys'])|{failure['url_key']})
den['blocked_artifacts']=sorted(set(den['blocked_artifacts'])|{'fc80df4469c8556fed45357cea8ba65f0c97535e','fast neighbor joining','fast neighbour joining'})
den['records'].append(dict(url=read(A/'get-fastnj-plan.json')['url'],reason=dict(status=failure['error'],artifact='Elias-Lagergren Fast Neighbor Joining ICALP2005',restriction=restriction),evidence=dict(path=str(A/'guard-ledger.jsonl'),sha256=sha(A/'guard-ledger.jsonl'),failed_receipt_sha256=sha(A/'get_fastnj.receipt.json'))))
# All integrity assertions precede documentary integration/preparation writes.
save(P/'tree-reconstruction-radius-source-parent-integration-sol-r1.json',record);denpath=ROOT/'inherited-denials-r507.json';save(denpath,den)
base=read(ROOT/'r496-config.json');base.update(number=497,protected_peers=['expanded-corpus-r496','weighted-zero-sum-source-review-sol-r1'],peer_routing_files=['selection-routing-r496.json','selection-routing-weighted-zero-sum-review-r1.json'],denials=str(denpath),quarantined_discovery_numbers=[395,463,466,482],year_floor=2000,candidate_pool=400)
base['steering']+='\n'+summary+'\nNEW '+restriction+'\n';save(ROOT/'r497-config.json',base)
spec=importlib.util.spec_from_file_location('discovery_constructor',ROOT/'prepare_discovery_packet.py');module=importlib.util.module_from_spec(spec);spec.loader.exec_module(module);newready=module.prepare(base)
allow=read(Path(newready['lane'])/'historical-results-allowlist.json');forbidden=('formal','code-loop','code_loop','polynexus','crown','bunkbed','tournament','hat-bipartite')
for name in allow:
 rel=Path(name).relative_to(P);assert not any(t in part.lower() for part in rel.parts for t in forbidden)
 assert not any(part in {f'expanded-corpus-r{x}' for x in [395,463,466,482]}|{f'expanded-corpus-r{x}-parent-integration.json' for x in [395,463,466,482]} for part in rel.parts)
save(ROOT/'tree-radius-review-completion-boundary-delta.json',dict(utc=now,message=summary+' NEW '+restriction,new_protected_peer='expanded-corpus-r497',immutable_worker_inputs_unchanged=True))
print(json.dumps(dict(files=105,frozen=30,events=dict(counts),budget=budget,ready=newready,accepted_new=57,credit=0)))
