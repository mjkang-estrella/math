"""Documentary integrity, expert credit adjudication and disjoint metadata selection only."""
import os,resource
os.sched_setaffinity(0,sorted(os.sched_getaffinity(0))[:2])
resource.setrlimit(resource.RLIMIT_CPU,(120,120))
resource.setrlimit(resource.RLIMIT_AS,(6*1024**3,6*1024**3))
from pathlib import Path
import json,hashlib,datetime,re,collections,importlib.util
ROOT=Path(__file__).resolve().parent;P=ROOT.parent
def read(p):return json.loads(p.read_text())
def dg(b):return hashlib.sha256(b).hexdigest()
def sha(p):return dg(p.read_bytes())
def save(p,v):
 assert not p.exists(),str(p)
 p.write_text(json.dumps(v,indent=2)+'\n')
now=datetime.datetime.now(datetime.timezone.utc).isoformat()
assert read(P/'ledger.json')['accepted_new']==57
def manifest(a,name,count,terminal,exfield):
 m=read(a/name);assert len(m['files'])==count
 names=set()
 for x in m['files']:
  n=x['path'];assert n not in names and not Path(n).is_absolute() and '..' not in Path(n).parts;names.add(n)
  q=a/n;assert not q.is_symlink() and sha(q)==x['sha256'] and q.stat().st_size==x['bytes'],n
 ex=m[exfield];assert set(ex)=={name,terminal+'.receipt.json',terminal+'.output.txt'}
 inventory=set()
 for q in a.rglob('*'):
  assert not q.is_symlink()
  if q.is_file():inventory.add(str(q.relative_to(a)))
 assert inventory==names|set(ex)
 return ex
def frozen(a,count):
 f=read(a/'frozen-inputs.json');assert len(f)==count
 assert all(Path(n).is_relative_to(a) and sha(Path(n))==h for n,h in f.items())
 before=read(a/'frozen-before.json');after=read(a/'frozen-after.json')
 assert before['count']==after['count']==count and before['mismatches']==after['mismatches']==[]
def receipts(a,failures):
 out=[]
 for q in sorted(a.glob('*.receipt.json')):
  v=read(q);assert v['cwd']==str(a) and v['cpu_limit_s']==115 and v['as_limit_bytes']==6*1024**3 and v['group_rss_guard_bytes']==6*1024**3 and v['deadline_s']==130 and len(v['affinity'])<=2 and v['killed'] is None
  assert v['exit']==failures.get(q.name,0),(a.name,q.name,v['exit'])
  out.append(dict(path=q.name,sha256=sha(q),exit=v['exit']))
 return out
def search(a,calls,queries,maxcalls,maxqueries,response_names):
 budget=read(a/'search-budget.json');assert budget==dict(calls_used=calls,queries_used=queries,maximum_calls=maxcalls,maximum_queries=maxqueries,charged_before_call=True)
 charges=[json.loads(s) for s in (a/'search-charges.jsonl').read_text().splitlines()];assert len(charges)==calls
 prev=dict(calls_used=0,queries_used=0,maximum_calls=maxcalls,maximum_queries=maxqueries,charged_before_call=True)
 for i,c in enumerate(charges,1):
  assert c['sequence']==i and c['before']==prev and sha(a/c['plan'])==c['plan_sha256'] and read(a/c['plan'])['queries']==c['queries']
  nxt=dict(prev,calls_used=i,queries_used=prev['queries_used']+len(c['queries']));assert c['after']==nxt;prev=nxt
  assert len((a/response_names[i-1]).read_text())>1000
 assert prev==budget and sha(a/'charge_search.py')==sha(ROOT/'charge_search.py')
 return budget
def guard(a,plans,ids,counts,pdfs):
 byhash={dg(json.dumps(read(q),sort_keys=True).encode()):read(q) for q in plans}
 events=[];previous='0'*64
 for i,line in enumerate((a/'guard-ledger.jsonl').read_bytes().splitlines(keepends=True)):
  e=json.loads(line);assert e['seq']==i and e['previous']==previous;previous=dg(line);events.append(e)
  if e['event']=='success':
   q=a/e['destination'];assert sha(q)==e['sha256'] and q.stat().st_size==e['bytes']
  if e['event']=='attempt':assert e['plan_sha256'] in byhash and e['url'].startswith('https://') and '/server/api/' not in e['url'] and set(e['routes'])<=set(map(str,ids))
 actual=collections.Counter(e['event'] for e in events);assert actual==counts
 assert sum((a/e['destination']).read_bytes().startswith(b'%PDF') for e in events if e['event']=='success')==pdfs
 return events
chunks={}
def corpus(prov,pathfield='chunk'):
 q=Path(prov[pathfield]);assert q.is_relative_to(P.parent/'lanes/pi-mathdb-full-corpus-inventory-r301/corpus')
 if str(q) not in chunks:
  data=q.read_bytes();chunks[str(q)]=(dg(data),data.splitlines(keepends=True))
 h,lines=chunks[str(q)];assert h==prov['chunk_sha256'];raw=lines[prov['line']-1]
 assert raw.endswith(b'\n') and prov['newline'] is True and dg(raw)==prov['raw_sha256']
 obj=json.loads(raw);tokens=re.findall(rb'"statement"\s*:\s*("(?:[^"\\]|\\.)*")',raw);assert len(tokens)==1
 return raw,obj,tokens[0]

R=P/'planar-laplacian-congruence-source-review-sol-r1'
ready=read(ROOT/'planar-laplacian-review-r1-ready.json');assert sha(R/'TASK.txt')==ready['task_sha256']
rex=manifest(R,'SHA256-MANIFEST.json',130,'seal','terminal_self_exclusions');frozen(R,30)
rrec=receipts(R,{'scopes_c.receipt.json':1,'get_final.receipt.json':1});assert read(R/'seal.receipt.json')['exit']==0
rbudget=search(R,1,2,2,6,['search01-fullresponse.json'])
revents=guard(R,list((R/'plans').glob('get*.json')),[328851],dict(attempt=4,success=2,redirect=1,unavailable=1),1)
prov=read(R/'inputs/provenance328851.json');raw,obj,token=corpus(prov)
assert raw==(R/'inputs/original328851.raw.jsonl').read_bytes() and obj==read(R/'inputs/literal328851.json')==read(R/'reservation.json')['rows'][0] and obj['mathdb_id']==328851
assert token.decode()==prov['statement_token'] and dg(token)==prov['token_sha256'] and dg(obj['statement'].encode())==prov['decoded_statement_sha256']
family=read(R/'family-comparison.json');assert len(family)==96 and all(x['exact_supplied_scope'] and x['comparison'] and x['decision'] for x in family)
rreview=read(R/'review.json');assert rreview['328851']['recommendation']=='EXCLUDE_ROUTINE_APPLICATION' and rreview['328851']['credit']==0
source=read(R/'source-map.json')['328851'];prior_success=next(e for e in revents if e.get('destination')=='sources/bacher1997.pdf')
assert prior_success['url']==source['prior']['url']=='https://numdam.org/item/10.24033/bsmf.2303.pdf'
failure=next(e for e in revents if e['event']=='unavailable');assert failure['status']==403
unavailable=read(R/'NEW-UNAVAILABLE.json')

A=P/'expanded-corpus-r506';route=read(ROOT/'selection-routing-r506.json')
assert sha(A/'TASK.txt')==route['task_sha256'] and sha(A/'reservation.json')==route['reservation_sha256']
aex=manifest(A,'manifest.json',137,'manifest-finalize','terminal_noncircular_self_exclusions');frozen(A,13)
arec=receipts(A,{});assert read(A/'manifest-finalize.receipt.json')['exit']==0
abudget=search(A,3,9,3,9,['search-one-response.json','search-two-response.json','search-three-response.json'])
ids=read(A/'reservation.json')['ids'];gates=read(A/'results.json');assert len(ids)==20 and set(ids)==set(map(int,gates))
provenance=read(A/'original-objects.json');assert len(provenance)==20
sources={}
for v in provenance:
 raw,obj,token=corpus(v,'path');mid=obj['mathdb_id'];assert mid in ids and mid not in sources
 assert raw.decode()==v['raw'] and (A/'originals'/f'{mid}.jsonl').read_bytes()==raw
 assert token.decode()==v['statement_token'] and dg(token)==v['statement_token_sha256'] and json.loads(token)==obj['statement']==v['statement'] and dg(obj['statement'].encode())==v['statement_utf8_sha256']
 sources[mid]=obj['source_url']
aevents=guard(A,list(A.glob('plan-*.json')),ids,dict(attempt=8,success=8),7)
history=read(A/'history-access.json');allow=read(A/'historical-results-allowlist.json');assert len(history)==861
for v in history:
 rel=Path(v['path']).relative_to(P)
 assert not any(t in part.lower() for part in rel.parts for t in ['formal','code-loop','code_loop','polynexus','crown','bunkbed','tournament','hat-bipartite'])
 assert not any(f'expanded-corpus-r{n}' in v['path'] for n in [395,463,466,482]) and v['path'] in allow and allow[v['path']]==v['sha256']

rsummary='328851 independent cached-literal/full ordinary proof PASS; ROOT EXCLUDE significant-discovery credit as COMPLETE ROUTINE APPLICATION of authenticated Bacher-de la Harpe-Nagnibeda1997 BSMF125(2) Proposition8 integral cut/flow sphere-duality theorem. Reviewer read actual statement/proof/integral bases and supplied full integral saturation/root-basis/full-singular-radical lift with loops/multiplicity/singleton retained; no mathematical gap reported. NOT domain correction, NOT earlier verbatim printed Conjecture4.11 solution, NOT shortness-only exclusion; full deliberate all-graphs conjecture and genuine bridges strongest positive dissent preserved. No new structural invariant/regime beyond exact earlier theorem reduction found. Original cachedv3 PASS, officialmetadata identifies2026J.Combinatorics17(3)389-415 finalDOI10.4310/JOC.260511223458 but302->publisher403 bodyunread; final/correction HOLD separate and not needed for routine objection. All96trusted scopes personally compared,boundednonmatch.130ownmanifestfiles30frozen1corpusbinding96scope rows verified,31runnerreceipts including get_final1/scopes_c1,4GEThops2payloads1PDF1HTML1redirect1HTTP403,1search2strings. Actualvisual/deepread/source-map limits and unknown native/transient/writer peaks retained. No formal dispatch,credit0.'
asummary='r506 zero qualified survivors.343508 AUTHOR full fixedt,l all-prime-power higher-wise normgraph second-moment proof and COMPLETE source exact degree/pair-codegree-to-target routine-adaptation bridge; no independent PASS, no matching earlier exact printed refutation/solution claimed, source explicitConj2 positive dissent preserved.352235 AUTHOR all-root walkbasis/outer-product bridge from ORourke-Touri2015 all-standard-basis controllability to full Terwilliger under uniform LABELLED model; routine recommendation only, source measure fidelity limitation unpaid.348800 connected hitting-probability calculation differs from actual Newman netflow, disconnected/fullmodel unpaid; no nearby repairedendpointcredit. Other17originals unread.137files20corpusbindings13frozen861savedhistory names verified;8GETsuccesses7PDF1HTML,3search9strings,nonewdenial. No figures/whole-body/importeddeep proof/current registry clearance. Author deductions and zero-credit recommendations retained, no independent/family/formal/acceptance PASS.'
recordr=dict(utc=now,mathdb_id=328851,source_lane=str(R),task_sha256=sha(R/'TASK.txt'),manifest_sha256=sha(R/'SHA256-MANIFEST.json'),verified_manifest_files=130,verified_frozen_bindings=30,verified_original_bindings=[328851],verified_saved_scope_comparisons=96,review=rreview,source_map=source,runner_receipts=rrec,guard_events=dict(collections.Counter(e['event'] for e in revents)),search_budget=rbudget,scientific_summary=rsummary,root_disposition='EXCLUDE_ROUTINE_APPLICATION_COMPLETE_1997_PRIMARY_BRIDGE',credit=0,accepted_new=57,target_new=60,formal_dispatch=False,terminal_self_exclusions=rex,root_scope='Documentary integrity and expert credit adjudication; no root mathematical solving/programs/Lean/checkers.')
recorda=dict(utc=now,source_lane=str(A),task_reservation_genesis_verified=True,manifest_sha256=sha(A/'manifest.json'),verified_manifest_files=137,verified_original_bindings=ids,verified_frozen_bindings=13,source_url_by_id=sources,all20_gates=gates,runner_receipts=arec,guard_events=dict(collections.Counter(e['event'] for e in aevents)),search_budget=abudget,verified_saved_history_names=861,scientific_summary=asummary,root_disposition='ZERO_QUALIFIED_SURVIVORS_AUTHOR_ROUTINE_PROPOSALS_NOT_INDEPENDENT_PASS',credit=0,accepted_new=57,target_new=60,formal_dispatch=False,terminal_self_exclusions=aex,root_scope='Documentary integrity/routing only; no root mathematical solving/programs/Lean/checkers.')
den=read(ROOT/'inherited-denials-r517.json');den['utc']=now;den['root_planar_laplacian328851_review_scope']=rsummary;den['root_r506_scope']=asummary
restriction=unavailable['restriction']+' Original1409.5853,allversions and exact2026 finalDOI10.4310/JOC.260511223458 are the same closed work; no final correction or metadata delivery by another route. Distinct Bacher1997 is not denied.'
den['blocked_keys']=sorted(set(den['blocked_keys'])|{failure['url_key'],'doi.org/10.4310/JOC.260511223458','arxiv.org/abs/1409.5853','arxiv.org/pdf/1409.5853'})
den['blocked_artifacts']=sorted(set(den['blocked_artifacts'])|{'graph invariants from ideas in physics and number theory','1409.5853','10.4310/joc.260511223458'})
den['records'].append(dict(url=failure['url'],reason=dict(status=403,artifact=unavailable['work'],restriction=restriction),evidence=dict(path=str(R/'NEW-UNAVAILABLE.json'),sha256=sha(R/'NEW-UNAVAILABLE.json'),guard_sha256=sha(R/'guard-ledger.jsonl'))))
# Only now begin root integration/preparation mutations.
save(P/'planar-laplacian-congruence-source-parent-integration-r1.json',recordr);save(P/'expanded-corpus-r506-parent-integration.json',recorda)
denpath=ROOT/'inherited-denials-r518.json';save(denpath,den)
base=read(ROOT/'r507-config.json')
base.update(number=508,protected_peers=['expanded-corpus-r507','expanded-corpus-r509'],completed_discovery_numbers=sorted(set(base['completed_discovery_numbers'])|{506}),peer_routing_files=['selection-routing-r507.json'],denials=str(denpath))
base['excluded_ids']=sorted(set(base['excluded_ids'])|{328851,343508,352235,348800})
base['excluded_sources']=sorted(set(base['excluded_sources'])|{'https://arxiv.org/abs/1409.5853'})
base['steering']+='\n'+rsummary+'\n'+asummary+'\nNEW '+restriction+'\n'
save(ROOT/'r508-config.json',base)
constructor=Path(base['metadata_constructor']);assert sha(constructor)=='37d7074c7f226a4f4940ce2b5a59c57e2b1a39ffdc339f1917cab5e68549c76b'
assert sha(Path(base['metadata_selector']))=='677992b5a6b1b17e45afbb3ae30f11548a37531593082819165278ee7d65ebed'
spec=importlib.util.spec_from_file_location('discovery_soft',constructor);module=importlib.util.module_from_spec(spec);spec.loader.exec_module(module)
ready508=module.prepare(base)
base509=dict(base);base509.update(number=509,protected_peers=['expanded-corpus-r507','expanded-corpus-r508'],peer_routing_files=['selection-routing-r507.json','selection-routing-r508.json'])
save(ROOT/'r509-config.json',base509);ready509=module.prepare(base509)
for ready in [ready508,ready509]:
 for name in read(Path(ready['lane'])/'historical-results-allowlist.json'):
  rel=Path(name).relative_to(P)
  assert not any(t in part.lower() for part in rel.parts for t in ['formal','code-loop','code_loop','polynexus','crown','bunkbed','tournament','hat-bipartite'])
  assert not any(part in ready['active_peers'] or part in {f'expanded-corpus-r{n}' for n in [395,463,466,482]}|{f'expanded-corpus-r{n}-parent-integration.json' for n in [395,463,466,482]} for part in rel.parts)
save(ROOT/'planar-review-r506-completion-boundary-delta.json',dict(utc=now,message=rsummary+'\n'+asummary+'\nNEW '+restriction,new_protected_peers=['expanded-corpus-r508','expanded-corpus-r509'],immutable_worker_inputs_unchanged=True,credit=0,accepted_new=57,root_documentary_deviations=['Initial compact schema diagnostic exited1 by indexing list-form original-objects as a dictionary; corrected in a smaller exact read before any integration/preparation write.']))
print(json.dumps(dict(review_files=130,discovery_files=137,frozen=43,corpus_bindings=21,scope_comparisons=96,readies=[ready508,ready509],credit=0,accepted_new=57)))
