"""Root documentary integrity and disjoint metadata-only selection; no mathematics."""
import os,resource
os.sched_setaffinity(0,sorted(os.sched_getaffinity(0))[:2]);resource.setrlimit(resource.RLIMIT_CPU,(120,120));resource.setrlimit(resource.RLIMIT_AS,(6*1024**3,6*1024**3))
from pathlib import Path
import json,hashlib,datetime,collections,re,importlib.util,base64
P=Path(__file__).resolve().parent.parent;ROOT=P/'root-intake-r60';A=P/'expanded-corpus-r497'
def sha(q):return hashlib.sha256(q.read_bytes()).hexdigest()
def dg(b):return hashlib.sha256(b).hexdigest()
def read(q):return json.loads(q.read_text())
def save(q,d):
 assert not q.exists(),str(q)
 q.write_text(json.dumps(d,indent=2)+'\n')
now=datetime.datetime.now(datetime.timezone.utc).isoformat();assert read(P/'ledger.json')['accepted_new']==57
route=read(ROOT/'selection-routing-r497.json');assert sha(A/'TASK.txt')==route['task_sha256'] and sha(A/'reservation.json')==route['reservation_sha256']
m=read(A/'MANIFEST.json');entries=m['files'];assert len(entries)==127
for n,v in entries.items():
 assert not Path(n).is_absolute() and '..' not in Path(n).parts
 q=A/n;assert not q.is_symlink() and sha(q)==v['sha256'] and q.stat().st_size==v['bytes'],n
ex=m['terminal_noncircular_self_exclusions'];assert set(ex)=={'MANIFEST.json','terminal_manifest.receipt.json','terminal_manifest.output.txt'}
actual=set()
for q in A.rglob('*'):
 assert not q.is_symlink()
 if q.is_file():actual.add(str(q.relative_to(A)))
assert actual==set(entries)|set(ex)
frozen=read(A/'frozen-inputs.json');assert len(frozen)==13 and all(Path(n).parent==A and sha(Path(n))==h for n,h in frozen.items())
after=read(A/'frozen-after.json');before=read(A/'frozen-before.json');assert before['count']==after['count']==13 and before['mismatches']==after['mismatches']==[]
gates=read(A/'results.json');prov=read(A/'literal-provenance.json');ids=read(A/'reservation.json')['ids'];assert len(ids)==len(prov)==20 and set(ids)==set(map(int,gates))=={r['id'] for r in prov}
chunks={};sources={}
for row in prov:
 key=str(row['id']);q=Path(row['chunk']);assert q.is_relative_to(P.parent/'lanes/pi-mathdb-full-corpus-inventory-r301/corpus')
 if str(q) not in chunks:
  b=q.read_bytes();chunks[str(q)]=(dg(b),b.splitlines(keepends=True))
 h,lines=chunks[str(q)];assert h==row['chunk_sha256'];raw=lines[row['line']-1];obj=json.loads(raw)
 assert row['newline'] is True and raw.endswith(b'\n') and dg(raw)==row['raw_line_sha256'] and (A/'originals'/f'{key}.jsonl').read_bytes()==raw and obj['mathdb_id']==row['id']
 tokens=re.findall(rb'"statement"\s*:\s*("(?:[^"\\]|\\.)*")',raw);assert len(tokens)==1;token=tokens[0]
 st=row['string_tokens']['statement'];assert token.decode()==st['raw'] and dg(token)==st['sha256'] and json.loads(token)==obj['statement']==gates[key]['literal']['statement'] and dg(obj['statement'].encode())==st['decoded_sha256'];sources[key]=obj['source_url']
receipts=[]
for q in sorted(A.glob('*.receipt.json')):
 v=read(q);assert v['cwd']==str(A) and v['cpu_limit_s']==115 and v['as_limit_bytes']==6*1024**3 and v['group_rss_guard_bytes']==6*1024**3 and v['deadline_s']==130 and len(v['affinity'])<=2 and v['killed'] is None
 receipts.append(dict(path=q.name,sha256=sha(q),exit=v['exit']))
assert read(A/'terminal_manifest.receipt.json')['exit']==0
budget=read(A/'search-budget.json');assert budget==dict(calls_used=3,queries_used=9,maximum_calls=3,maximum_queries=9,charged_before_call=True)
charges=[json.loads(s) for s in (A/'search-charges.jsonl').read_text().splitlines()];assert len(charges)==3
prev=dict(calls_used=0,queries_used=0,maximum_calls=3,maximum_queries=9,charged_before_call=True)
for i,c in enumerate(charges,1):
 assert c['sequence']==i and c['before']==prev and sha(A/c['plan'])==c['plan_sha256'] and read(A/c['plan'])['queries']==c['queries']
 nxt=dict(prev,calls_used=i,queries_used=prev['queries_used']+len(c['queries']));assert c['after']==nxt;prev=nxt
 response=(A/f'search{i}-response.json').read_text();assert len(response)>1000
assert prev==budget and sha(A/'charge_search.py')==sha(ROOT/'charge_search.py')
events=[];prev='0'*64
plans={dg(json.dumps(read(q),sort_keys=True).encode()):read(q) for q in (A/'plans').glob('get-*.json')}
for i,line in enumerate((A/'guard-ledger.jsonl').read_bytes().splitlines(keepends=True)):
 e=json.loads(line);assert e['seq']==i and e['previous']==prev;prev=dg(line);events.append(e)
 if e['event']=='success':
  q=A/e['destination'];assert sha(q)==e['sha256'] and q.stat().st_size==e['bytes']
 if e['event']=='attempt':assert e['plan_sha256'] in plans and '/server/api/' not in e['url'] and e['url'].startswith('https://') and set(e['routes'])<=set(map(str,ids))
counts=collections.Counter(e['event'] for e in events);assert counts==dict(attempt=7,success=5,redirect=1,unavailable=1)
history=read(A/'history-access.json');allow=read(A/'historical-results-allowlist.json');assert len(history)==839
forbidden=('formal','code-loop','code_loop','polynexus','crown','bunkbed','tournament','hat-bipartite')
for x in history:
 rel=Path(x['path']).relative_to(P)
 assert not any(t in part.lower() for part in rel.parts for t in forbidden)
 assert not any(f'expanded-corpus-r{n}' in x['path'] for n in [395,463,466,482]) and x['path'] in allow and allow[x['path']]==x['sha256']
assert all((A/e['destination']).read_bytes().startswith(b'%PDF') for e in events if e['event']=='success')
failure=next(e for e in events if e['event']=='unavailable');assert failure['url_key']=='oldlemon.cs.elte.hu/egres/open/Cyclic_orderings_of_matroids' and 'TimeoutError' in failure['error']
assert read(A/'get_egres.receipt.json')['exit']==1 and read(A/'recover_egres.receipt.json')['exit']==1
summary='380677 exact volume-recurrence equivalence helpers,388051 direct-sum cyclic-order closure and380621 finite-state distance-coloring decidability leave full intended endpoints unpaid;388061 literal decidability versus intended efficient exact-matching problem distinguished, specific Du public-proof body partially read HOLD not adopted theorem.316201 actual Dobson-Morris Definitions15/16/24 andCorollary33 proof read supplies full directed unit-circulant CI-to-multiplier application public0, n1/emptyS boundaries handled and deep group input attributed not audited. Neighbor380674 totalvolume does not imply facet recurrence. No full candidate or formal dispatch.127 files20 raw/token/decoded bindings13 frozen839 saved historical names verified;7GET hops5PDF1redirect1timeout/unavailable,3 searches9strings. Early get_egres yield and recover FileNotFoundError, omitted external timeout140 wrappers, truncated outputs and sampled/native/transient limits retained, no universal procedural PASS; no observed resource kill or manual retry.'
restriction='ENTIRE exact Egres Cyclic orderings of matroids page at lemon.cs.elte.hu/egres/open/Cyclic_orderings_of_matroids and oldlemon.cs.elte.hu/egres/open/Cyclic_orderings_of_matroids ALL NEW host/query/version/cache/mirror/DOI/API/body/metadata deliveries unavailable after redirected oldlemon timeout. No retry/alternate identity/indirect recovery. Distinct earlier-acquired split-matroid paper is not this failed page; not a blanket denial of all matroid/cyclic-order papers or all Egres pages.'
record=dict(utc=now,source_lane=str(A),task_reservation_genesis_verified=True,manifest_sha256=sha(A/'MANIFEST.json'),verified_manifest_files=127,verified_original_bindings=ids,verified_frozen_bindings=13,source_url_by_id=sources,all20_gates=gates,runner_receipts=receipts,guard_events=dict(counts),search_budget=budget,root_disposition='ZERO_QUALIFIED_FULL_SCOPE_SURVIVORS',scientific_summary=summary,credit=0,accepted_new=57,target_new=60,formal_dispatch=False,terminal_self_exclusions=ex,root_scope='Documentary provenance/integrity/routing only; no root mathematical solving/programs/Lean/checkers.')
den=read(ROOT/'inherited-denials-r509.json');den['utc']=now;den['root_r497_scope']=summary
den['blocked_keys']=sorted(set(den['blocked_keys'])|{'lemon.cs.elte.hu/egres/open/Cyclic_orderings_of_matroids',failure['url_key']})
den['blocked_artifacts']=sorted(set(den['blocked_artifacts'])|{'egres/open/cyclic_orderings_of_matroids','egres cyclic orderings of matroids page'})
den['records'].append(dict(url=failure['url'],reason=dict(status=failure['error'],artifact='Exact Egres Cyclic orderings of matroids page',restriction=restriction),evidence=dict(path=str(A/'guard-ledger.jsonl'),sha256=sha(A/'guard-ledger.jsonl'),failed_receipt_sha256=sha(A/'get_egres.receipt.json'))))
# All integrity assertions precede integration and disjoint packet preparation.
save(P/'expanded-corpus-r497-parent-integration.json',record);denpath=ROOT/'inherited-denials-r510.json';save(denpath,den)
base=read(ROOT/'r498-config.json');base.update(number=499,protected_peers=['expanded-corpus-r498','prime-like-goldbach-source-review-sol-r1'],completed_discovery_numbers=sorted(set(base['completed_discovery_numbers'])|{496,497}),peer_routing_files=['selection-routing-r498.json','selection-routing-prime-like-goldbach-review-r1.json'],denials=str(denpath),quarantined_discovery_numbers=[395,463,466,482],year_floor=1900,candidate_pool=1000)
base['excluded_ids']=sorted(set(base['excluded_ids'])|{368088});base['excluded_sources']=sorted(set(base['excluded_sources'])|{'https://arxiv.org/abs/2504.14353','https://arxiv.org/abs/2211.02865'})
base['steering']+='\n'+den['root_r496_scope']+'\n'+summary+'\nNEW '+restriction+'\n';save(ROOT/'r499-config.json',base)
spec=importlib.util.spec_from_file_location('discovery_constructor',ROOT/'prepare_discovery_packet.py');module=importlib.util.module_from_spec(spec);spec.loader.exec_module(module);ready=module.prepare(base)
allow=read(Path(ready['lane'])/'historical-results-allowlist.json')
for name in allow:
 rel=Path(name).relative_to(P);assert not any(t in part.lower() for part in rel.parts for t in forbidden)
 assert not any(part in {f'expanded-corpus-r{x}' for x in [395,463,466,482]}|{f'expanded-corpus-r{x}-parent-integration.json' for x in [395,463,466,482]} for part in rel.parts)
save(ROOT/'r497-completion-boundary-delta.json',dict(utc=now,message=summary+' NEW '+restriction,new_protected_peer='expanded-corpus-r499',immutable_worker_inputs_unchanged=True))
print(json.dumps(dict(files=127,frozen=13,bindings=20,receipts=len(receipts),events=dict(counts),ready=ready,credit=0,accepted_new=57)))
