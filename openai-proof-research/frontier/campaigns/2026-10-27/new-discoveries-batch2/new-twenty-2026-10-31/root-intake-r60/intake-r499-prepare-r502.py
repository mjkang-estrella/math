"""Root documentary integrity and disjoint metadata-only selection; no mathematics."""
import os,resource
os.sched_setaffinity(0,sorted(os.sched_getaffinity(0))[:2]);resource.setrlimit(resource.RLIMIT_CPU,(120,120));resource.setrlimit(resource.RLIMIT_AS,(6*1024**3,6*1024**3))
from pathlib import Path
import json,hashlib,datetime,collections,re,importlib.util,base64
P=Path(__file__).resolve().parent.parent;ROOT=P/'root-intake-r60';A=P/'expanded-corpus-r499'
def sha(q):return hashlib.sha256(q.read_bytes()).hexdigest()
def dg(b):return hashlib.sha256(b).hexdigest()
def read(q):return json.loads(q.read_text())
def save(q,d):
 assert not q.exists(),str(q)
 q.write_text(json.dumps(d,indent=2)+'\n')
now=datetime.datetime.now(datetime.timezone.utc).isoformat();assert read(P/'ledger.json')['accepted_new']==57
route=read(ROOT/'selection-routing-r499.json');assert sha(A/'TASK.txt')==route['task_sha256'] and sha(A/'reservation.json')==route['reservation_sha256']
m=read(A/'manifest.json');entries=m['files'];assert len(entries)==112
for n,v in entries.items():
 assert not Path(n).is_absolute() and '..' not in Path(n).parts
 q=A/n;assert not q.is_symlink() and sha(q)==v['sha256'] and q.stat().st_size==v['bytes'],n
ex=m['terminal_noncircular_self_exclusions'];assert set(ex)=={'manifest.json','manifest_build.receipt.json','manifest_build.output.txt'}
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
 assert row['newline'] is True and raw.endswith(b'\n') and dg(raw)==row['raw_sha256'] and base64.b64decode(row['raw_base64'],validate=True)==raw and obj['mathdb_id']==row['id']
 tokens=re.findall(rb'"statement"\s*:\s*("(?:[^"\\]|\\.)*")',raw);assert len(tokens)==1;token=tokens[0]
 assert token==base64.b64decode(row['statement_token_base64'],validate=True) and dg(token)==row['statement_token_sha256'] and json.loads(token)==obj['statement']==row['statement'] and dg(obj['statement'].encode())==row['statement_sha256'];sources[key]=obj['source_url']
receipts=[]
for q in sorted(A.glob('*.receipt.json')):
 v=read(q);assert v['cwd']==str(A) and v['cpu_limit_s']==115 and v['as_limit_bytes']==6*1024**3 and v['group_rss_guard_bytes']==6*1024**3 and v['deadline_s']==130 and len(v['affinity'])<=2 and v['killed'] is None
 receipts.append(dict(path=q.name,sha256=sha(q),exit=v['exit']))
assert read(A/'manifest_build.receipt.json')['exit']==0
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
counts=collections.Counter(e['event'] for e in events);assert counts==dict(attempt=8,success=8)
history=read(A/'history-access.json');allow=read(A/'historical-results-allowlist.json');assert len(history)==844
forbidden=('formal','code-loop','code_loop','polynexus','crown','bunkbed','tournament','hat-bipartite')
for x in history:
 rel=Path(x['path']).relative_to(P)
 assert not any(t in part.lower() for part in rel.parts for t in forbidden)
 assert not any(f'expanded-corpus-r{n}' in x['path'] for n in [395,463,466,482]) and x['path'] in allow and allow[x['path']]==x['sha256']
assert sum((A/e['destination']).read_bytes().startswith(b'%PDF') for e in events if e['event']=='success')==7
manual=read(A/'manual-outcomes.json');assert manual['transport']==200 and manual['guard_event']=='success unchanged' and manual['manual_classification']=='UNAVAILABLE_CHALLENGE_SCRIPT_BEYOND_GUARD_PREFIX' and manual['proof_evidence'] is False
assert manual['url']=='https://www.erdosproblems.com/809' and sha(A/manual['destination'])==manual['payload_sha256']
challenge_offset=(A/manual['destination']).read_bytes().lower().find(b'challenge-platform');assert challenge_offset>=12000
assert read(A/'read_antichain_rainbow.receipt.json')['exit']==1 and read(A/'manifest_build.receipt.json')['exit']==0
summary='391260 actual He-Tang2602.09803v2 public n0 bounds/necessary two-branch antichain reduction and label construction helpers leave sharp all-r threshold unpaid; concrete Botnet secondary-term claim proof unread HOLD.391290 author two-clique limsup1/8 is public helper; actual2609.38286v1 Cor1.2 exact all-fixed-k>=3 public claim bridge read but full certificate/transfer/BCM proof unaudited matching-public-proof HOLD, not independent exclusion.391409 public k>=5 construction does not pay k4 arbitrary-r edge robustness; blowup/join shortcuts fail, all-scope PARK.388112 actual2511.13709v1Th1.9 prints full finite-edge-cover counterexample/proof, public0.388086 actual2306.10631v3 restricted infinite orientation results do not pay arbitrary infinite2k.391315 criticality ambiguity/public proof certificates incompletely audited HOLD.390713 actual2609.40192v2 conditional exact r5,k4 full-girth public-refutation bridge paid, key construction proof unread HOLD. No qualified survivor.112 ownfiles20 corpus bindings13 frozen844 saved historical names verified;8GET transport-success7PDF1HTML,3 searches9queries. Missingbs4 readexit1/stdlb recovery and empty substring output retained; no sourcefinal/body/figure/registry clearance inferred.'
restriction='ENTIRE exact ErdosProblems809 current entry at www.erdosproblems.com/809 unavailable for ALL NEW host/query/version/cache/mirror/DOI/API/body/METADATA or indirect deliveries after manual challenge-bearing HTML classification. Transport200/guard success remains immutable, not overwritten as network failure. No retry/script execution/browser/account/API or alternate recovery of page. Challenge-platform marker was at byte31752 beyond first12000 inspected by guard. Distinct clean primary papers including2609.38286 are not this page and are not blanket denied; their proof limits remain explicit.'
record=dict(utc=now,source_lane=str(A),task_reservation_genesis_verified=True,manifest_sha256=sha(A/'manifest.json'),verified_manifest_files=112,verified_original_bindings=ids,verified_frozen_bindings=13,source_url_by_id=sources,all20_gates=gates,runner_receipts=receipts,guard_events=dict(counts),search_budget=budget,manual_challenge_outcome=manual,challenge_marker_offset=challenge_offset,root_disposition='ZERO_QUALIFIED_FULL_SCOPE_SURVIVORS',scientific_summary=summary,procedure='Own manifest/provenance/counter/hashchain/history-name verification only; no root external history follow. Manual unavailable page classification retained without guard-history rewrite. No actual challenge bypass/retry observed; no universal procedural or deep proof PASS. Source/public matching claims remain their exact read-scope HOLDs.',credit=0,accepted_new=57,target_new=60,formal_dispatch=False,terminal_self_exclusions=ex,root_scope='Documentary integrity/routing only; no root mathematical solving/programs/Lean/checkers.')
den=read(ROOT/'inherited-denials-r511.json');den['utc']=now;den['root_r499_scope']=summary
den['blocked_keys']=sorted(set(den['blocked_keys'])|{'www.erdosproblems.com/809'})
den['blocked_artifacts']=sorted(set(den['blocked_artifacts'])|{'erdosproblems.com/809','erdosproblems809 current page'})
den['records'].append(dict(url=manual['url'],reason=dict(status=manual['manual_classification'],artifact=manual['artifact'],restriction=restriction),evidence=dict(path=str(A/'manual-outcomes.json'),sha256=sha(A/'manual-outcomes.json'),payload_sha256=manual['payload_sha256'],guard_sha256=sha(A/'guard-ledger.jsonl'))))
# All checks precede integration/preparation writes.
save(P/'expanded-corpus-r499-parent-integration.json',record);denpath=ROOT/'inherited-denials-r512.json';save(denpath,den)
base=read(ROOT/'r501-config.json');base.update(number=502,protected_peers=['expanded-corpus-r500','expanded-corpus-r501'],completed_discovery_numbers=sorted(set(base['completed_discovery_numbers'])|{499}),peer_routing_files=['selection-routing-r500.json','selection-routing-r501.json'],denials=str(denpath),quarantined_discovery_numbers=[395,463,466,482],year_floor=1900,candidate_pool=1000)
base['steering']+='\n'+summary+'\nNEW '+restriction+'\n';save(ROOT/'r502-config.json',base)
spec=importlib.util.spec_from_file_location('discovery_constructor',ROOT/'prepare_discovery_packet.py');module=importlib.util.module_from_spec(spec);spec.loader.exec_module(module);ready=module.prepare(base)
allow=read(Path(ready['lane'])/'historical-results-allowlist.json')
for name in allow:
 rel=Path(name).relative_to(P);assert not any(t in part.lower() for part in rel.parts for t in forbidden)
 assert not any(part in {f'expanded-corpus-r{x}' for x in [395,463,466,482]}|{f'expanded-corpus-r{x}-parent-integration.json' for x in [395,463,466,482]} for part in rel.parts)
save(ROOT/'r499-completion-boundary-delta.json',dict(utc=now,message=summary+' NEW '+restriction,new_protected_peer='expanded-corpus-r502',immutable_worker_inputs_unchanged=True))
print(json.dumps(dict(files=112,frozen=13,bindings=20,receipts=len(receipts),events=dict(counts),ready=ready,accepted_new=57,credit=0)))
