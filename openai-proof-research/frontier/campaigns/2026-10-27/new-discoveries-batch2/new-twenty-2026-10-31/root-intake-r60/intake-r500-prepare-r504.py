"""Root documentary integrity and disjoint metadata-only selection; no mathematics."""
import os,resource
os.sched_setaffinity(0,sorted(os.sched_getaffinity(0))[:2]);resource.setrlimit(resource.RLIMIT_CPU,(120,120));resource.setrlimit(resource.RLIMIT_AS,(6*1024**3,6*1024**3))
from pathlib import Path
import json,hashlib,datetime,collections,re,importlib.util
P=Path(__file__).resolve().parent.parent;ROOT=P/'root-intake-r60';A=P/'expanded-corpus-r500'
def sha(q):return hashlib.sha256(q.read_bytes()).hexdigest()
def dg(b):return hashlib.sha256(b).hexdigest()
def read(q):return json.loads(q.read_text())
def save(q,d):
 assert not q.exists(),str(q)
 q.write_text(json.dumps(d,indent=2)+'\n')
now=datetime.datetime.now(datetime.timezone.utc).isoformat();assert read(P/'ledger.json')['accepted_new']==57
route=read(ROOT/'selection-routing-r500.json');assert sha(A/'TASK.txt')==route['task_sha256'] and sha(A/'reservation.json')==route['reservation_sha256']
m=read(A/'SHA256-MANIFEST.json');entries=m['files'];assert len(entries)==154
for n,v in entries.items():
 assert not Path(n).is_absolute() and '..' not in Path(n).parts
 q=A/n;assert not q.is_symlink() and sha(q)==v['sha256'] and q.stat().st_size==v['bytes'],n
ex=m['terminal_noncircular_self_exclusions'];assert set(ex)=={'SHA256-MANIFEST.json','final_manifest.receipt.json','final_manifest.output.txt'}
actual=set()
for q in A.rglob('*'):
 assert not q.is_symlink()
 if q.is_file():actual.add(str(q.relative_to(A)))
assert actual==set(entries)|set(ex)
frozen=read(A/'frozen-inputs.json');assert len(frozen)==13 and all(Path(n).parent==A and sha(Path(n))==h for n,h in frozen.items())
after=read(A/'frozen-after.json');before=read(A/'frozen-before.json');assert before['count']==after['count']==13 and before['mismatches']==after['mismatches']==[]
gates=read(A/'results.json');prov=read(A/'original-provenance.json');ids=read(A/'reservation.json')['ids'];assert len(ids)==len(prov)==20 and set(ids)==set(map(int,gates))==set(map(int,prov))
chunks={};sources={}
for key,row in prov.items():
 q=Path(row['chunk']);assert q.is_relative_to(P.parent/'lanes/pi-mathdb-full-corpus-inventory-r301/corpus')
 if str(q) not in chunks:
  b=q.read_bytes();chunks[str(q)]=(dg(b),b.splitlines(keepends=True))
 h,lines=chunks[str(q)];assert h==row['chunk_sha256'];raw=lines[row['line']-1];obj=json.loads(raw)
 assert row['newline'] is True and raw.endswith(b'\n') and dg(raw)==row['raw_sha256'] and (A/'originals'/f'{key}.jsonl').read_bytes()==raw and obj==row['record'] and obj['mathdb_id']==int(key)
 tokens=re.findall(rb'"statement"\s*:\s*("(?:[^"\\]|\\.)*")',raw);assert len(tokens)==1;token=tokens[0]
 assert token.decode()==row['token'] and dg(token)==row['token_sha256'] and json.loads(token)==obj['statement']==gates[key]['literal_gate']['statement']==row['statement'] and dg(obj['statement'].encode())==row['statement_sha256'];sources[key]=obj['source_url']
receipts=[]
for q in sorted(A.glob('*.receipt.json')):
 v=read(q);assert v['cwd']==str(A) and v['cpu_limit_s']==115 and v['as_limit_bytes']==6*1024**3 and v['group_rss_guard_bytes']==6*1024**3 and v['deadline_s']==130 and len(v['affinity'])<=2 and v['killed'] is None
 receipts.append(dict(path=q.name,sha256=sha(q),exit=v['exit']))
assert read(A/'final_manifest.receipt.json')['exit']==0
budget=read(A/'search-budget.json');assert budget==dict(calls_used=3,queries_used=9,maximum_calls=3,maximum_queries=9,charged_before_call=True)
charges=[json.loads(s) for s in (A/'search-charges.jsonl').read_text().splitlines()];assert len(charges)==3
prev=dict(calls_used=0,queries_used=0,maximum_calls=3,maximum_queries=9,charged_before_call=True)
for i,c in enumerate(charges,1):
 assert c['sequence']==i and c['before']==prev and sha(A/c['plan'])==c['plan_sha256'] and read(A/c['plan'])['queries']==c['queries']
 nxt=dict(prev,calls_used=i,queries_used=prev['queries_used']+len(c['queries']));assert c['after']==nxt;prev=nxt
 response=(A/f'search{i}-response.json').read_text();assert len(response)>1000
assert prev==budget and sha(A/'charge_search.py')==sha(ROOT/'charge_search.py')
events=[];prev='0'*64
plans={dg(json.dumps(read(q),sort_keys=True).encode()):read(q) for q in A.glob('get-*.json')}
for i,line in enumerate((A/'guard-ledger.jsonl').read_bytes().splitlines(keepends=True)):
 e=json.loads(line);assert e['seq']==i and e['previous']==prev;prev=dg(line);events.append(e)
 if e['event']=='success':
  q=A/e['destination'];assert sha(q)==e['sha256'] and q.stat().st_size==e['bytes']
 if e['event']=='attempt':assert e['plan_sha256'] in plans and '/server/api/' not in e['url'] and e['url'].startswith('https://') and set(e['routes'])<=set(map(str,ids))
counts=collections.Counter(e['event'] for e in events);assert counts==dict(attempt=10,success=10)
history=read(A/'history-access.json');allow=read(A/'historical-results-allowlist.json');assert len(history)==847
forbidden=('formal','code-loop','code_loop','polynexus','crown','bunkbed','tournament','hat-bipartite')
for x in history:
 rel=Path(x['path']).relative_to(P)
 assert not any(t in part.lower() for part in rel.parts for t in forbidden)
 assert not any(f'expanded-corpus-r{n}' in x['path'] for n in [395,463,466,482]) and x['path'] in allow and allow[x['path']]==x['sha256']
assert sum((A/e['destination']).read_bytes().startswith(b'%PDF') for e in events if e['event']=='success')==9
route_counts=collections.Counter(x for e in events if e['event']=='attempt' for x in e['routes']);assert max(route_counts.values())==2
manual=read(A/'manual-unavailable.json');page=A/'sources/prime-public.html';offset=page.read_bytes().lower().find(b'challenge-platform')
assert manual['sha256']==sha(page) and manual['marker_byte_zero_based']==offset==31670 and not manual['guard_failure'] and manual['network_stopped_on_detection'] and not manual['retry'] and not manual['proof_body_clearance']
summary='No full candidate. Sustained list-palette, empty-board/clique-game and general weighted Tamari routes retain exact unpaid lemmas; general-m Tamari needs residue-preserving interval bijection, PSPACE membership not either hardness conjecture.391261 source-own fattened-cubes bridge refutes middle clause only, not first clause/full literal;380800 disconnected equality issue retained as correction0; other small-range/local obstructions0. Fourteen assigned IDs received original-source passages from7 distinct originals,6 originals unread; actual list-color/comparable-pairs finals relevant passages read, no visual/whole-body/deep/currentcorrection completeness. Specific Leonard/Sorensen-Thomassen/Mader,Kostochka-Pyber,Green-Tao proof bodies unread HOLD.154 files20 corpus bindings13 frozen847 saved historical names verified;10GET transport-success9PDF1HTML,max2 perroute,3 searches9strings. ExactErdosProblems1187 challenge-bearing page manually closed, transport200/guard success unchanged, no actual bypass/retry. Late normalized source-alias reconciliation and truncated task/source displays/resource limits retained; no independent/family/acceptance PASS.'
restriction='ENTIRE EXACT ErdosProblems1187 current entry https://www.erdosproblems.com/1187 unavailable for ALL NEW host/query/version/cache/mirror/DOI/API/body/METADATA or indirect deliveries after manual challenge-bearing HTML classification at byte31670 beyond guard12000 prefix. Transport200/guard success retained unchanged; no guard failure invented. Network stopped on detection; no retry/JS/browser/account/API/alternate recovery of PAGE. Distinct original1980 paper is not this page and not denied by this classification; not a blanket denial of ErdosProblems/prime-combinatorics works.'
record=dict(utc=now,source_lane=str(A),task_reservation_genesis_verified=True,manifest_sha256=sha(A/'SHA256-MANIFEST.json'),verified_manifest_files=154,verified_original_bindings=ids,verified_frozen_bindings=13,source_url_by_id=sources,all20_gates=gates,runner_receipts=receipts,guard_events=dict(counts),route_get_counts=dict(route_counts),search_budget=budget,manual_unavailable=manual,root_disposition='ZERO_QUALIFIED_FULL_SCOPE_SURVIVORS',scientific_summary=summary,credit=0,accepted_new=57,target_new=60,formal_dispatch=False,terminal_self_exclusions=ex,root_scope='Documentary integrity/routing only; no root mathematical solving/programs/Lean/checkers.')
den=read(ROOT/'inherited-denials-r513.json');den['utc']=now;den['root_r500_scope']=summary
den['blocked_keys']=sorted(set(den['blocked_keys'])|{'www.erdosproblems.com/1187'})
den['blocked_artifacts']=sorted(set(den['blocked_artifacts'])|{'erdosproblems.com/1187','erdosproblems1187 current page'})
den['records'].append(dict(url='https://www.erdosproblems.com/1187',reason=dict(status='Manual challenge-bearing HTML; transport200/guard success unchanged',artifact=manual['artifact'],restriction=restriction),evidence=dict(path=str(A/'manual-unavailable.json'),sha256=sha(A/'manual-unavailable.json'),payload_sha256=sha(page),guard_sha256=sha(A/'guard-ledger.jsonl'))))
# All verification precedes documentary integration or new selection preparation.
save(P/'expanded-corpus-r500-parent-integration.json',record);denpath=ROOT/'inherited-denials-r514.json';save(denpath,den)
base=read(ROOT/'r503-config.json');base.update(number=504,protected_peers=['expanded-corpus-r502','expanded-corpus-r503'],completed_discovery_numbers=sorted(set(base['completed_discovery_numbers'])|{500}),peer_routing_files=['selection-routing-r502.json','selection-routing-r503.json'],denials=str(denpath),quarantined_discovery_numbers=[395,463,466,482],year_floor=1900,candidate_pool=1000)
base['steering']+='\n'+summary+'\nNEW '+restriction+'\n';save(ROOT/'r504-config.json',base)
constructor=Path(base['metadata_constructor']);assert constructor==ROOT/'prepare_discovery_packet_soft_asymp.py' and sha(constructor)=='37d7074c7f226a4f4940ce2b5a59c57e2b1a39ffdc339f1917cab5e68549c76b'
assert sha(Path(base['metadata_selector']))=='677992b5a6b1b17e45afbb3ae30f11548a37531593082819165278ee7d65ebed'
spec=importlib.util.spec_from_file_location('discovery_constructor_soft',constructor);module=importlib.util.module_from_spec(spec);spec.loader.exec_module(module);ready=module.prepare(base)
al=read(Path(ready['lane'])/'historical-results-allowlist.json')
for name in al:
 rel=Path(name).relative_to(P);assert not any(t in part.lower() for part in rel.parts for t in forbidden)
 assert not any(part in {f'expanded-corpus-r{x}' for x in [395,463,466,482]}|{f'expanded-corpus-r{x}-parent-integration.json' for x in [395,463,466,482]} for part in rel.parts)
save(ROOT/'r500-completion-boundary-delta.json',dict(utc=now,message=summary+' NEW '+restriction,new_protected_peer='expanded-corpus-r504',immutable_worker_inputs_unchanged=True))
print(json.dumps(dict(files=154,frozen=13,bindings=20,receipts=len(receipts),events=dict(counts),route_get_counts=dict(route_counts),ready=ready,accepted_new=57,credit=0)))
