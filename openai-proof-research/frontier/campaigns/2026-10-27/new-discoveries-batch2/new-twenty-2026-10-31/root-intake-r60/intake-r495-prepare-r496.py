"""Root documentary integrity and disjoint metadata-only selection; no mathematics."""
import os,resource
os.sched_setaffinity(0,sorted(os.sched_getaffinity(0))[:2]);resource.setrlimit(resource.RLIMIT_CPU,(120,120));resource.setrlimit(resource.RLIMIT_AS,(6*1024**3,6*1024**3))
from pathlib import Path
import json,hashlib,datetime,collections,re,importlib.util,base64
P=Path(__file__).resolve().parent.parent;ROOT=P/'root-intake-r60';A=P/'expanded-corpus-r495'
def sha(q):return hashlib.sha256(q.read_bytes()).hexdigest()
def dg(b):return hashlib.sha256(b).hexdigest()
def read(q):return json.loads(q.read_text())
def save(q,d):
 assert not q.exists(),str(q)
 q.write_text(json.dumps(d,indent=2)+'\n')
now=datetime.datetime.now(datetime.timezone.utc).isoformat();assert read(P/'ledger.json')['accepted_new']==57
route=read(ROOT/'selection-routing-r495.json');assert sha(A/'TASK.txt')==route['task_sha256'] and sha(A/'reservation.json')==route['reservation_sha256']
m=read(A/'SHA256-MANIFEST.json');entries=m['files'];assert len(entries)==128
for n,v in entries.items():
 assert not Path(n).is_absolute() and '..' not in Path(n).parts
 q=A/n;assert not q.is_symlink() and sha(q)==v['sha256'] and q.stat().st_size==v['bytes'],n
ex=m['terminal_noncircular_self_exclusions'];assert set(ex)=={'SHA256-MANIFEST.json','terminal_manifest.receipt.json','terminal_manifest.output.txt'}
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
 assert row['newline'] is True and raw.endswith(b'\n') and dg(raw)==row['raw_sha256'] and base64.b64decode(row['raw_base64'],validate=True)==raw and obj==row['record'] and (A/'originals'/f'{key}.jsonl').read_bytes()==raw and obj['mathdb_id']==row['id']
 tokens=re.findall(rb'"statement"\s*:\s*("(?:[^"\\]|\\.)*")',raw);assert len(tokens)==1;token=tokens[0]
 assert token==base64.b64decode(row['token_base64'],validate=True) and dg(token)==row['token_sha256'] and json.loads(token)==obj['statement']==gates[key]['literal_gate']['statement'] and dg(obj['statement'].encode())==row['statement_sha256'];sources[key]=obj['source_url']
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
 response=(A/f'search-response-{i}.json').read_text();assert len(response)>1000
assert prev==budget and sha(A/'charge_search.py')==sha(ROOT/'charge_search.py')
events=[];prev='0'*64
plans={dg(json.dumps(read(q),sort_keys=True).encode()):read(q) for q in A.glob('get-*.json')}
for i,line in enumerate((A/'guard-ledger.jsonl').read_bytes().splitlines(keepends=True)):
 e=json.loads(line);assert e['seq']==i and e['previous']==prev;prev=dg(line);events.append(e)
 if e['event']=='success':
  q=A/e['destination'];assert sha(q)==e['sha256'] and q.stat().st_size==e['bytes']
 if e['event']=='attempt':assert e['plan_sha256'] in plans and '/server/api/' not in e['url'] and e['url'].startswith('https://') and set(e['routes'])<=set(map(str,ids))
counts=collections.Counter(e['event'] for e in events);assert counts==dict(attempt=6,success=6)
history=read(A/'history-access.json')['accesses'];allow=read(A/'historical-results-allowlist.json');assert len(history)==832
forbidden=('formal','code-loop','code_loop','polynexus','crown','bunkbed','tournament','hat-bipartite')
for x in history:
 rel=Path(x['path']).relative_to(P)
 assert not any(t in part.lower() for part in rel.parts for t in forbidden)
 assert not any(f'expanded-corpus-r{n}' in x['path'] for n in [395,463,466,482]) and x['path'] in allow and allow[x['path']]==x['sha256']
assert all((A/e['destination']).read_bytes().startswith(b'%PDF') for e in events if e['event']=='success')
summary='379623 exact coefficient contraction/cactus subfamily helpers leave general invertible exchange/rooted-K4 obstruction unpaid.379841 deleted-edge-height fiber connectivity and379842 planar-piece quartic connectivity unpaid.320185 sourceTheorem7/OOM inclusion supplies intended existential factorization attribution0, not arbitrary greedy2w theorem; inversion/source-definition tension retained0.320886 actual source explicit tropical/Kapranov refutation public0.327213 source own odd-complete formula contradicts characterization, correction0, failed first coloring preserved and repaired.317594 actual final CLP exponential theorem supplies logarithmic target public0. Fourteen originals unread, Horn specific prior proofs unread HOLD.128 files20 corpus bindings13 frozen832 saved historical names verified;6PDF GET successes3 searches9 strings,no new denials. Documentary substring lookup failure and tool-composition syntax failure retained, material recovery paid; no universal process/whole-body PASS.'
record=dict(utc=now,source_lane=str(A),task_reservation_genesis_verified=True,manifest_sha256=sha(A/'SHA256-MANIFEST.json'),verified_manifest_files=128,verified_original_bindings=ids,verified_frozen_bindings=13,source_url_by_id=sources,all20_gates=gates,runner_receipts=receipts,guard_events=dict(counts),search_budget=budget,root_disposition='ZERO_QUALIFIED_FULL_SCOPE_SURVIVORS',scientific_summary=summary,credit=0,accepted_new=57,target_new=60,formal_dispatch=False,terminal_self_exclusions=ex,root_scope='Documentary integrity/routing only; no root mathematical solving/programs/Lean/checkers.')
den=read(ROOT/'inherited-denials-r505.json');den['utc']=now;den['root_r495_scope']=summary;denpath=ROOT/'inherited-denials-r506.json'
# All verification precedes integration or new packet preparation.
save(P/'expanded-corpus-r495-parent-integration.json',record);save(denpath,den)
base=read(ROOT/'r495-config.json');base.update(number=496,protected_peers=['tree-reconstruction-radius-source-review-sol-r1','weighted-zero-sum-source-review-sol-r1'],completed_discovery_numbers=sorted(set(base['completed_discovery_numbers'])|{493,494,495}),quarantined_discovery_numbers=[395,463,466,482],denials=str(denpath),peer_routing_files=['selection-routing-tree-reconstruction-radius-review-r1.json','selection-routing-weighted-zero-sum-review-r1.json'],year_floor=2000,candidate_pool=400)
base['excluded_ids']=sorted(set(base['excluded_ids'])|{317672,316875});base['excluded_sources']=sorted(set(base['excluded_sources'])|{'https://arxiv.org/abs/0809.0158','https://arxiv.org/abs/0711.4074'})
base['steering']+='\n'+den['root_r493_scope']+'\n'+den['root_r494_scope']+'\n'+summary+'\nAll inherited Ni-Tatikonda and Csaji full-work closures retained. Both current targeted reviews protected entirely, no author-source reuse.\n'
save(ROOT/'r496-config.json',base);spec=importlib.util.spec_from_file_location('discovery_constructor',ROOT/'prepare_discovery_packet.py');module=importlib.util.module_from_spec(spec);spec.loader.exec_module(module);ready=module.prepare(base)
al=read(Path(ready['lane'])/'historical-results-allowlist.json')
for name in al:
 rel=Path(name).relative_to(P);assert not any(t in part.lower() for part in rel.parts for t in forbidden)
 assert not any(part in {f'expanded-corpus-r{x}' for x in [395,463,466,482]}|{f'expanded-corpus-r{x}-parent-integration.json' for x in [395,463,466,482]} for part in rel.parts)
save(ROOT/'r495-completion-boundary-delta.json',dict(utc=now,message=summary,new_protected_peer='expanded-corpus-r496',immutable_worker_inputs_unchanged=True))
print(json.dumps(dict(files=128,frozen=13,bindings=20,receipts=len(receipts),ready=ready,credit=0,accepted_new=57)))
