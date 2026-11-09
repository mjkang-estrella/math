"""Root documentary integrity and substantive-credit adjudication; no mathematics."""
import os,resource
os.sched_setaffinity(0,sorted(os.sched_getaffinity(0))[:2]);resource.setrlimit(resource.RLIMIT_CPU,(120,120));resource.setrlimit(resource.RLIMIT_AS,(6*1024**3,6*1024**3))
from pathlib import Path
import json,hashlib,datetime,collections,importlib.util
P=Path(__file__).resolve().parent.parent;ROOT=P/'root-intake-r60';A=P/'weighted-zero-sum-source-review-sol-r1'
def read(p):return json.loads(p.read_text())
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def dg(b):return hashlib.sha256(b).hexdigest()
def save(p,d):
 assert not p.exists(),str(p)
 p.write_text(json.dumps(d,indent=2)+'\n')
now=datetime.datetime.now(datetime.timezone.utc).isoformat();assert read(P/'ledger.json')['accepted_new']==57
ready=read(ROOT/'weighted-zero-sum-review-r1-ready.json');assert sha(A/'TASK.txt')==ready['task_sha256']
m=read(A/'SHA256-MANIFEST.json');entries=m['files'];assert len(entries)==m['count']==132
for n,v in entries.items():
 assert not Path(n).is_absolute() and '..' not in Path(n).parts
 q=A/n;assert not q.is_symlink() and sha(q)==v['sha256'] and q.stat().st_size==v['bytes'],n
ex=m['excluded_exact'];assert set(ex)=={'SHA256-MANIFEST.json','manifest_final.receipt.json','manifest_final.output.txt'}
actual=set()
for q in A.rglob('*'):
 assert not q.is_symlink()
 if q.is_file():actual.add(str(q.relative_to(A)))
assert actual==set(entries)|set(ex)
fr=read(A/'frozen-inputs.json');assert len(fr)==33
for n,h in fr.items():assert Path(n).is_relative_to(A) and sha(Path(n))==h
for n in ['frozen-before.json','frozen-after.json']:
 v=read(A/n);assert v['count']==33 and v['mismatches']==[]
literal=read(A/'inputs/literal316875.json');assert json.loads((A/'inputs/original316875.raw.jsonl').read_text())==literal and literal['mathdb_id']==316875
receipts=[]
for q in sorted(A.glob('*.receipt.json')):
 v=read(q);assert v['cwd']==str(A) and v['cpu_limit_s']==115 and v['as_limit_bytes']==6*1024**3 and v['group_rss_guard_bytes']==6*1024**3 and v['deadline_s']==130 and len(v['affinity'])<=2 and v['killed'] is None
 receipts.append(dict(path=q.name,sha256=sha(q),exit=v['exit']))
assert len(receipts)==29 and read(A/'manifest_final.receipt.json')['exit']==0 and read(A/'scopes57_recover.receipt.json')['exit']==1
budget=read(A/'search-budget.json');assert budget==dict(calls_used=2,queries_used=6,maximum_calls=2,maximum_queries=6,charged_before_call=True)
charges=[json.loads(s) for s in (A/'search-charges.jsonl').read_text().splitlines()];assert len(charges)==2
prev=dict(budget,calls_used=0,queries_used=0)
for i,c in enumerate(charges,1):
 assert c['sequence']==i and c['before']==prev and sha(A/c['plan'])==c['plan_sha256'] and read(A/c['plan'])['queries']==c['queries'] and len(c['queries'])==3
 nxt=dict(prev,calls_used=i,queries_used=prev['queries_used']+3);assert c['after']==nxt;prev=nxt
 response=read(A/f'search-response-{i}.json');assert isinstance(response,(str,dict,list)) and len(json.dumps(response))>1000
assert prev==budget and sha(A/'charge_search.py')==sha(ROOT/'charge_search.py')
plans={dg(json.dumps(read(q),sort_keys=True).encode()):read(q) for q in A.glob('get-*.json')};events=[];previous='0'*64
for i,line in enumerate((A/'guard-ledger.jsonl').read_bytes().splitlines(keepends=True)):
 e=json.loads(line);assert e['seq']==i and e['previous']==previous;previous=dg(line);events.append(e)
 if e['event']=='attempt':assert e['plan_sha256'] in plans and e['routes']==['316875'] and e['url'].startswith('https://') and '/server/api/' not in e['url']
 if e['event']=='success':
  q=A/e['destination'];assert sha(q)==e['sha256'] and q.stat().st_size==e['bytes']
counts=collections.Counter(e['event'] for e in events);assert counts==dict(attempt=4,success=4)
assert sum((A/e['destination']).read_bytes().startswith(b'%PDF') for e in events if e['event']=='success')==2
review=read(A/'review.json');v=review['316875'];assert v['ordinary']['status']==v['source']['status']==v['literal']['status']=='PASS' and v['significance']['status']=='RECOMMEND_EXCLUDE_DOMAIN_CORRECTION' and v['acceptance']['credit']==0 and not v['prior']['exact_public_refutation_authenticated']
summary='316875 independent ordinary/literal/original-and-final-source PASS retained: all partial supports/injections negated by C4 sequence1,1,3,3 and weights1,2, actual finalCPC17Conj2.2 unrestricted integer weights, all6final pages personally read/visually checked. ROOT EXCLUDE from significant-discovery credit as NONUNIT-WEIGHT DOMAIN CORRECTION, adopting specialist assessment that scalar loss of invertibility/prime-square quotient defect returns to already-known individual-unit branch without new positive regime/sharp invariant/classification. Strong opposing case preserved: deliberately broader final conjecture genuinely refuted, odd-square quotient mechanism not even-parity-only, smallness alone not exclusion. NOT a corpus mistranscription, NOT authenticated earlier exact public refutation, NOT a completed prior-refutation adaptation exclusion. Actual0903.2810 theorem/proof and JTNB689 statements/examples bounded nonmatches, remaining classification proofs unread not used for exclusion. Reviewer authored unit-branch ordinary bridge not separately independently certified; no mathematical/acceptance credit assigned to it.57+39 bounded family comparison nonoverlap retained, all variants one uncredited family.132 files33 frozen verified,4 GET successes2PDF2HTML,2 searches6strings,no new denials. Documentary KeyError/truncation recovery and native/transient/writer limits retained.'
adjudication=dict(disposition='EXCLUDE_SIGNIFICANT_DISCOVERY_CREDIT_DOMAIN_CORRECTION',basis='Root adopts the completed independent reviewer substantive-credit recommendation under campaign domain-correction rule, preserving actual printed-conjecture falsehood and opposing case.',not_claimed=['Earlier exact printed refutation','Implicit unit hypothesis in actual source','Worldwide novelty clearance','Shortness-only exclusion','Independent certification of newly authored unit-branch bridge','Formal/campaign acceptance'])
record=dict(utc=now,source_lane=str(A),task_genesis_verified=True,manifest_sha256=sha(A/'SHA256-MANIFEST.json'),verified_manifest_files=132,verified_frozen_bindings=33,runner_receipts=receipts,receipt_exit_counts=dict(collections.Counter(str(x['exit']) for x in receipts)),guard_events=dict(counts),search_budget=budget,review=review,root_adjudication=adjudication,scientific_summary=summary,credit=0,accepted_new=57,formal_dispatch=False,terminal_self_exclusions=ex,root_scope='Documentary verification/credit adjudication/routing only; no root mathematical solving/programs/Lean/checkers.')
den=read(ROOT/'inherited-denials-r507.json');den['utc']=now;den['root_weighted_zero_sum316875_review_scope']=summary;denpath=ROOT/'inherited-denials-r508.json'
# All assertions precede completed intake writes/new selection preparation.
save(P/'weighted-zero-sum-source-parent-integration-sol-r1.json',record);save(denpath,den)
base=read(ROOT/'r497-config.json');base.update(number=498,protected_peers=['expanded-corpus-r496','expanded-corpus-r497'],peer_routing_files=['selection-routing-r496.json','selection-routing-r497.json'],denials=str(denpath),quarantined_discovery_numbers=[395,463,466,482],year_floor=1900,candidate_pool=1000)
base['steering']+='\n'+summary+'\nNo formal redispatch/credit for316875 or parameter variants; no new denial inferred from a credit exclusion.\n';save(ROOT/'r498-config.json',base)
spec=importlib.util.spec_from_file_location('discovery_constructor',ROOT/'prepare_discovery_packet.py');module=importlib.util.module_from_spec(spec);spec.loader.exec_module(module);newready=module.prepare(base)
allow=read(Path(newready['lane'])/'historical-results-allowlist.json');forbidden=('formal','code-loop','code_loop','polynexus','crown','bunkbed','tournament','hat-bipartite')
for name in allow:
 rel=Path(name).relative_to(P);assert not any(t in part.lower() for part in rel.parts for t in forbidden)
 assert not any(part in {f'expanded-corpus-r{x}' for x in [395,463,466,482]}|{f'expanded-corpus-r{x}-parent-integration.json' for x in [395,463,466,482]} for part in rel.parts)
save(ROOT/'weighted-review-completion-boundary-delta.json',dict(utc=now,message=summary,new_protected_peer='expanded-corpus-r498',immutable_worker_inputs_unchanged=True))
print(json.dumps(dict(files=132,frozen=33,events=dict(counts),budget=budget,ready=newready,accepted_new=57,credit=0)))
