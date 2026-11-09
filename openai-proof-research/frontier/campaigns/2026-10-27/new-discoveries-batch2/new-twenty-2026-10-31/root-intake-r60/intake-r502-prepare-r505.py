"""Root documentary integrity and disjoint metadata-only selection; no mathematics."""
import os,resource
os.sched_setaffinity(0,sorted(os.sched_getaffinity(0))[:2]);resource.setrlimit(resource.RLIMIT_CPU,(120,120));resource.setrlimit(resource.RLIMIT_AS,(6*1024**3,6*1024**3))
from pathlib import Path
import json,hashlib,datetime,collections,re,importlib.util
P=Path(__file__).resolve().parent.parent;ROOT=P/'root-intake-r60';A=P/'expanded-corpus-r502'
def sha(q):return hashlib.sha256(q.read_bytes()).hexdigest()
def dg(b):return hashlib.sha256(b).hexdigest()
def read(q):return json.loads(q.read_text())
def save(q,d):
 assert not q.exists(),str(q)
 q.write_text(json.dumps(d,indent=2)+'\n')
now=datetime.datetime.now(datetime.timezone.utc).isoformat();assert read(P/'ledger.json')['accepted_new']==57
route=read(ROOT/'selection-routing-r502.json');assert sha(A/'TASK.txt')==route['task_sha256'] and sha(A/'reservation.json')==route['reservation_sha256']
m=read(A/'SHA256-MANIFEST.json');entries=m['files'];assert len(entries)==112
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
gates=read(A/'results.json');prov=read(A/'original-provenance.json');ids=read(A/'reservation.json')['ids'];assert len(ids)==len(prov)==20 and set(ids)==set(map(int,gates))=={r['id'] for r in prov}
chunks={};sources={}
for row in prov:
 key=str(row['id']);q=Path(row['chunk']);assert q.is_relative_to(P.parent/'lanes/pi-mathdb-full-corpus-inventory-r301/corpus')
 if str(q) not in chunks:
  b=q.read_bytes();chunks[str(q)]=(dg(b),b.splitlines(keepends=True))
 h,lines=chunks[str(q)];assert h==row['chunk_sha256'];raw=lines[row['line']-1];obj=json.loads(raw)
 assert row['newline'] is True and raw.endswith(b'\n') and dg(raw)==row['raw_sha256'] and raw.decode()==row['raw_line_utf8'] and f'originals/{key}.jsonl' in entries and (A/'originals'/f'{key}.jsonl').read_bytes()==raw and obj['mathdb_id']==row['id']
 tokens=re.findall(rb'"statement"\s*:\s*("(?:[^"\\]|\\.)*")',raw);assert len(tokens)==1;token=tokens[0]
 assert token.decode()==row['raw_statement_token'] and dg(token)==row['raw_statement_token_sha256'] and json.loads(token)==obj['statement']==gates[key]['literal']['statement']==row['decoded_statement'] and dg(obj['statement'].encode())==row['decoded_statement_utf8_sha256'];sources[key]=obj['source_url']
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
plans={dg(json.dumps(read(q),sort_keys=True).encode()):read(q) for q in A.glob('get-*-plan.json')}
for i,line in enumerate((A/'guard-ledger.jsonl').read_bytes().splitlines(keepends=True)):
 e=json.loads(line);assert e['seq']==i and e['previous']==prev;prev=dg(line);events.append(e)
 if e['event']=='success':
  q=A/e['destination'];assert sha(q)==e['sha256'] and q.stat().st_size==e['bytes']
 if e['event']=='attempt':assert e['plan_sha256'] in plans and '/server/api/' not in e['url'] and e['url'].startswith('https://') and set(e['routes'])<=set(map(str,ids))
counts=collections.Counter(e['event'] for e in events);assert counts==dict(attempt=4,success=3,unavailable=1)
history=read(A/'history-access.json');allow=read(A/'historical-results-allowlist.json');assert len(history)==849
forbidden=('formal','code-loop','code_loop','polynexus','crown','bunkbed','tournament','hat-bipartite')
for x in history:
 rel=Path(x['path']).relative_to(P)
 assert not any(t in part.lower() for part in rel.parts for t in forbidden)
 assert not any(f'expanded-corpus-r{n}' in x['path'] for n in [395,463,466,482]) and x['path'] in allow and allow[x['path']]==x['sha256']
assert sum((A/e['destination']).read_bytes().startswith(b'%PDF') for e in events if e['event']=='success')==2
failure=next(e for e in events if e['event']=='unavailable');oddurl='https://mathweb.ucsd.edu/~erdosproblems/erdos/newproblems/OddCycleOfLargeChromaticNumber.html';assert failure['url']==oddurl and 'SSLCertVerificationError' in failure['error']
manual=read(A/'manual-unavailable.json');assert len(manual['records'])==2 and manual['network_policy_breach_observed'] is False and manual['records'][1]['url']=='https://www.erdosproblems.com/881'
page=A/'sources/basis881.html';offset=page.read_bytes().lower().find(b'challenge-platform');assert offset==30499 and page.read_text().lower().find('challenge-platform')==30497
assert read(A/'get_odd_source.receipt.json')['exit']==1 and read(A/'terminal_manifest.receipt.json')['exit']==0
summary='No full candidate.391145 complete conditional BFS parity/path-span equivalence leaves DFS compatibility unpaid;390745 complement/neighborhood bound and explicit3-sun failure do not pay full maximal-trianglefree extraction;391292 forest greedy embedding/source lexicographic amplification partial, all-graph classification unpaid;391353 k1 sparse deletion helper leaves all-k extendibility unpaid. Actual Chung45pagegraphproblems relevant71/34 passages only and Axenovich-Clemen2209.13867v2Sections1-4 read, external Sidon/difference/Peluse inputs attributed not audited. Specific Svyable Infinite Deletions from Strongly Minimal Additive Bases MainTh6 proof/scope unread HOLD, no manuscript theorem adopted.112 files20 raw/token/decoded corpus bindings13 frozen849 saved historical names verified;4GET attempts2PDF1HTMLsuccess1TLSunavailable,3search9strings. ExactUCSDodd-cycle webpage TLS failure andErdosProblems881 challenge-bearing page closed; distinct clean graph/rainbow papers not banned. Material read/task truncation recovery and native/transient/writer limits retained, no sourcefinal/registry/deep-proof PASS.'
tlsrestriction='ENTIRE identified Original OddCycleOfLargeChromaticNumber problem webpage at mathweb.ucsd.edu/~erdosproblems/erdos/newproblems/OddCycleOfLargeChromaticNumber.html ALL NEW hosts/versions/query/cache/mirror/DOI/API/body/METADATA or indirect deliveries unavailable after TLS certificate verification failure. No retry/certificate bypass/alternate delivery. Distinct already-acquired Chung graph-problems PDF and clean Axenovich-Clemen rainbow paper are not this failed page; not a blanket ban on odd-cycle or UCSD mathematical works.'
pagerestriction='ENTIRE EXACT ErdosProblems881 current entry https://www.erdosproblems.com/881 unavailable for ALL NEW host/query/version/cache/mirror/DOI/API/body/METADATA or indirect deliveries after manual challenge-bearing HTML classification beyond guard12000 prefix. Root measured actual byte30499; author30497 is the decoded character index, preserved as reporting erratum. Transport200/guard success stays immutable, not reclassified as guard network failure. No retry/JS/browser/account/API/alternate recovery of PAGE; no scientific proof clearance from page. Distinct actual primary works are not blanket denied.'
record=dict(utc=now,source_lane=str(A),task_reservation_genesis_verified=True,manifest_sha256=sha(A/'SHA256-MANIFEST.json'),verified_manifest_files=112,verified_original_bindings=ids,verified_frozen_bindings=13,source_url_by_id=sources,all20_gates=gates,runner_receipts=receipts,guard_events=dict(counts),search_budget=budget,manual_unavailable=manual,challenge_marker_offset=offset,marker_position_erratum=dict(author_reported_byte=30497,actual_decoded_character_index=30497,actual_utf8_byte_offset=30499,evidence_unchanged=True),root_disposition='ZERO_QUALIFIED_FULL_SCOPE_SURVIVORS',scientific_summary=summary,credit=0,accepted_new=57,target_new=60,formal_dispatch=False,terminal_self_exclusions=ex,root_scope='Documentary provenance/integrity/routing only; no root mathematical solving/programs/Lean/checkers.')
den=read(ROOT/'inherited-denials-r514.json');den['utc']=now;den['root_r502_scope']=summary
den['blocked_keys']=sorted(set(den['blocked_keys'])|{failure['url_key'],'www.erdosproblems.com/881'})
den['blocked_artifacts']=sorted(set(den['blocked_artifacts'])|{'oddcycleoflargechromaticnumber.html','erdosproblems.com/881','erdosproblems881 current page'})
for url,artifact,restriction,status in [(oddurl,manual['records'][0]['identity'],tlsrestriction,failure['error']),('https://www.erdosproblems.com/881',manual['records'][1]['identity'],pagerestriction,'Manual challenge-bearing HTML; transport200/guard success unchanged')]:
 den['records'].append(dict(url=url,reason=dict(status=status,artifact=artifact,restriction=restriction),evidence=dict(path=str(A/'manual-unavailable.json'),sha256=sha(A/'manual-unavailable.json'),guard_sha256=sha(A/'guard-ledger.jsonl'),payload_sha256=sha(page) if url.endswith('/881') else None)))
# All checks precede integration/preparation writes.
save(P/'expanded-corpus-r502-parent-integration.json',record);denpath=ROOT/'inherited-denials-r515.json';save(denpath,den)
base=read(ROOT/'r504-config.json');base.update(number=505,protected_peers=['expanded-corpus-r503','expanded-corpus-r504'],completed_discovery_numbers=sorted(set(base['completed_discovery_numbers'])|{502}),peer_routing_files=['selection-routing-r503.json','selection-routing-r504.json'],denials=str(denpath),quarantined_discovery_numbers=[395,463,466,482],year_floor=1900,candidate_pool=1000)
base['excluded_sources']=sorted(set(base['excluded_sources'])|{oddurl,'https://www.erdosproblems.com/881','https://www.erdosproblems.com/809','https://www.erdosproblems.com/1187'})
base['steering']+='\n'+summary+'\nNEW '+tlsrestriction+'\nNEW '+pagerestriction+'\n';save(ROOT/'r505-config.json',base)
constructor=Path(base['metadata_constructor']);assert constructor==ROOT/'prepare_discovery_packet_soft_asymp.py' and sha(constructor)=='37d7074c7f226a4f4940ce2b5a59c57e2b1a39ffdc339f1917cab5e68549c76b'
assert sha(Path(base['metadata_selector']))=='677992b5a6b1b17e45afbb3ae30f11548a37531593082819165278ee7d65ebed'
spec=importlib.util.spec_from_file_location('discovery_constructor_soft',constructor);module=importlib.util.module_from_spec(spec);spec.loader.exec_module(module);ready=module.prepare(base)
al=read(Path(ready['lane'])/'historical-results-allowlist.json')
for name in al:
 rel=Path(name).relative_to(P);assert not any(t in part.lower() for part in rel.parts for t in forbidden)
 assert not any(part in {f'expanded-corpus-r{x}' for x in [395,463,466,482]}|{f'expanded-corpus-r{x}-parent-integration.json' for x in [395,463,466,482]} for part in rel.parts)
save(ROOT/'r502-completion-boundary-delta.json',dict(utc=now,message=summary+' NEW '+tlsrestriction+' NEW '+pagerestriction,new_protected_peer='expanded-corpus-r505',immutable_worker_inputs_unchanged=True))
print(json.dumps(dict(files=112,frozen=13,bindings=20,receipts=len(receipts),events=dict(counts),ready=ready,accepted_new=57,credit=0)))
