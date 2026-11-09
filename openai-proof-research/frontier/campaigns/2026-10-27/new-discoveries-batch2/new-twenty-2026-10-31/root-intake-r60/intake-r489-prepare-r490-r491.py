"""Root documentary integrity and disjoint metadata-only selection; no mathematics."""
import os,resource
os.sched_setaffinity(0,sorted(os.sched_getaffinity(0))[:2]);resource.setrlimit(resource.RLIMIT_CPU,(120,120));resource.setrlimit(resource.RLIMIT_AS,(6*1024**3,6*1024**3))
from pathlib import Path
import json,hashlib,datetime,collections,re,importlib.util
P=Path(__file__).resolve().parent.parent;ROOT=P/'root-intake-r60';A=P/'expanded-corpus-r489'
def sha(q):return hashlib.sha256(q.read_bytes()).hexdigest()
def dg(b):return hashlib.sha256(b).hexdigest()
def read(q):return json.loads(q.read_text())
def save(q,d):
 assert not q.exists(),str(q)
 q.write_text(json.dumps(d,indent=2)+'\n')
now=datetime.datetime.now(datetime.timezone.utc).isoformat();assert read(P/'ledger.json')['accepted_new']==57
route=read(ROOT/'selection-routing-r489.json');assert sha(A/'TASK.txt')==route['task_sha256'] and sha(A/'reservation.json')==route['reservation_sha256']
m=read(A/'MANIFEST.json');entries={x['path']:x for x in m['files']};assert len(entries)==len(m['files'])==137
for n,v in entries.items():
 assert not Path(n).is_absolute() and '..' not in Path(n).parts
 q=A/n;assert not q.is_symlink() and sha(q)==v['sha256'] and q.stat().st_size==v['bytes'],n
ex=m['terminal_noncircular_self_exclusions'];assert set(ex)=={'MANIFEST.json','manifest_seal.receipt.json','manifest_seal.output.txt'}
actual=set()
for q in A.rglob('*'):
 assert not q.is_symlink()
 if q.is_file():actual.add(str(q.relative_to(A)))
assert actual==set(entries)|set(ex)
frozen=read(A/'frozen-inputs.json');assert len(frozen)==13 and all(Path(n).parent==A and sha(Path(n))==h for n,h in frozen.items())
after=read(A/'frozen-after.json');before=read(A/'frozen-before.json');assert before['count']==after['count']==13 and before['mismatches']==after['mismatches']==[]
gates=read(A/'results.json');literals=read(A/'literals.json');prov=read(A/'provenance.json');ids=read(A/'reservation.json')['ids'];assert len(ids)==len(prov)==20 and set(ids)==set(map(int,gates))==set(map(int,literals))=={r['id'] for r in prov}
chunks={};sources={}
for row in prov:
 key=str(row['id']);q=Path(row['chunk']);assert q.is_relative_to(P.parent/'lanes/pi-mathdb-full-corpus-inventory-r301/corpus')
 if str(q) not in chunks:
  b=q.read_bytes();chunks[str(q)]=(dg(b),b.splitlines(keepends=True))
 h,lines=chunks[str(q)];assert h==row['chunk_sha256'];raw=lines[row['line']-1];obj=json.loads(raw)
 assert row['newline'] is True and raw.endswith(b'\n') and dg(raw)==row['raw_sha256'] and (A/'originals'/f'{key}.jsonl').read_bytes()==raw and obj==literals[key] and obj['mathdb_id']==row['id']
 tokens=re.findall(rb'"statement"\s*:\s*("(?:[^"\\]|\\.)*")',raw);assert len(tokens)==1;token=tokens[0]
 assert token.decode()==row['token'] and dg(token)==row['token_sha256'] and json.loads(token)==obj['statement']==gates[key]['literal_gate']['statement'] and dg(obj['statement'].encode())==row['statement_sha256'];sources[key]=obj['source_url']
receipts=[]
for q in sorted(A.glob('*.receipt.json')):
 v=read(q);assert v['cwd']==str(A) and v['cpu_limit_s']==115 and v['as_limit_bytes']==6*1024**3 and v['group_rss_guard_bytes']==6*1024**3 and v['deadline_s']==130 and len(v['affinity'])<=2 and v['killed'] is None
 receipts.append(dict(path=q.name,sha256=sha(q),exit=v['exit']))
assert read(A/'manifest_seal.receipt.json')['exit']==0
budget=read(A/'search-budget.json');assert budget==dict(calls_used=2,queries_used=6,maximum_calls=3,maximum_queries=9,charged_before_call=True)
charges=[json.loads(s) for s in (A/'search-charges.jsonl').read_text().splitlines()];assert len(charges)==2
prev=dict(calls_used=0,queries_used=0,maximum_calls=3,maximum_queries=9,charged_before_call=True)
for i,c in enumerate(charges,1):
 assert c['sequence']==i and c['before']==prev and sha(A/c['plan'])==c['plan_sha256'] and read(A/c['plan'])['queries']==c['queries']
 nxt=dict(prev,calls_used=i,queries_used=prev['queries_used']+len(c['queries']));assert c['after']==nxt;prev=nxt
 response=read(A/f'search{i}-response.json');assert isinstance(response,str) and len(response)>1000
assert prev==budget and sha(A/'charge_search.py')==sha(ROOT/'charge_search.py')
events=[];prev='0'*64
plans={dg(json.dumps(read(q),sort_keys=True).encode()):read(q) for q in A.glob('get-*.json')}
for i,line in enumerate((A/'guard-ledger.jsonl').read_bytes().splitlines(keepends=True)):
 e=json.loads(line);assert e['seq']==i and e['previous']==prev;prev=dg(line);events.append(e)
 if e['event']=='success':
  q=A/e['destination'];assert sha(q)==e['sha256'] and q.stat().st_size==e['bytes'] and q.read_bytes().startswith(b'%PDF')
 if e['event']=='attempt':assert e['plan_sha256'] in plans and '/server/api/' not in e['url'] and e['url'].startswith('https://') and set(e['routes'])<=set(map(str,ids))
counts=collections.Counter(e['event'] for e in events);assert counts==dict(attempt=7,success=7)
history=read(A/'history-access.json');allow=read(A/'historical-results-allowlist.json');assert len(history)==816
forbidden=('formal','code-loop','code_loop','polynexus','crown','bunkbed','tournament','hat-bipartite')
for x in history:
 rel=Path(x['path']).relative_to(P)
 assert not any(t in part.lower() for part in rel.parts for t in forbidden)
 assert not any(f'expanded-corpus-r{n}' in x['path'] for n in [395,463,466,482]) and x['path'] in allow and allow[x['path']]==x['sha256']
summary='320916(i)authorfullcommon-zero-supportingtrianglefaceproof forallorientedcutpairs intendedn>=3andn2paid,notfulltarget:weightedpart(ii) simultaneousweight-triangle exposingfunctional/uniquedecompositionallmembershipcellsunpaid.320917someforcedthirdfacetnonedges/L-L/L-Mrelativeinteriorconstructions paid,allallowedM-M/M-T/T-Ttypes/diameter2/quotientridgebridgeunpaid.322777exacttwo-levelESPobjectiveconstraintreductionpaid,fullfeasibletwoconstraintsmoothingwithactivecoordinate/boundarycontrolunpaid.376549actualBencs1409.2527publicrealrootedproofplusnonnegativeconstant1negative-rootbridge0,originalSokalunreadnotmultivariateclaim.320040source1006.2560Th3.1strongerGroebnerproofexactpublic0;319494source1001.5077v2Cor6.3exactfourrankformulaspublic0,deepergeometryattributed/typosnotfreshindependentranktheorem.320265source1008.1837v3Section19.5immediaterefutation/figure20public0,diagramnotvisuallyaudited.'
record=dict(utc=now,source_lane=str(A),task_reservation_genesis_verified=True,manifest_sha256=sha(A/'MANIFEST.json'),verified_manifest_files=137,verified_original_bindings=sorted(ids),verified_frozen_bindings=13,source_url_by_id=sources,all20_gates=gates,runner_receipts=receipts,receipt_exit_counts=dict(collections.Counter(str(x['exit']) for x in receipts)),guard_events=dict(counts),search_budget=budget,root_disposition='ZERO_QUALIFIED_FULL_LITERAL_SURVIVORS',scientific_summary=summary,reading_limits='Fourteenassignedoriginalbodiesunread;followupBencs/ultrarigidnotoriginalfinalequivalence. Partial320916(i)notpromotedoverunpaid(ii). DeeperSchur/geometry/gluinganddiagramsnotindependentlycertified.',process='137ownfiles20raw/token/decodedbindings13frozen816savedhistorynamesverified,norootexternalhistoryfollow.7PDFGETsuccess0redirect/denial,2chargedsearch6queries/fullresponsesverified. Firstliteralextractorlookedforidnotmathdb_idreturnedzero,correcteddifferentreceiptwithoutreselection;oldoutputsretained. Sourceexcerptsrecoveredaftertruncation,nouniversalbody/telemetry/accessPASS;native/transient/writer/supervisorlimitsretained.',root_scope='Documentaryprovenance/integrity/routingonly,no root mathematical solving/programs/Lean/checkers.',credit=0,accepted_new=57,target_new=60,formal_dispatch=False,terminal_self_exclusions=ex)
delta='Completedr489zeroqualifiedfull-literalsurvivors. '+summary+'137files20bindings13frozen816savedhistorypathsverified,7PDFGETsuccess2search6queries,nonewdenials/dispatch/credit.57/60unchanged.'
den=read(ROOT/'inherited-denials-r497.json');den['utc']=now;den['root_r489_scope']=delta;denpath=ROOT/'inherited-denials-r498.json'
# All checks precede documentary writes/new disjoint discovery preparations.
save(P/'expanded-corpus-r489-parent-integration.json',record);save(denpath,den)
base=read(ROOT/'r489-config.json');base['completed_discovery_numbers']=sorted(set(base['completed_discovery_numbers'])|{488,489})
base['excluded_ids']=sorted(set(base['excluded_ids'])|{377665,378413})
base['excluded_sources']=sorted(set(base['excluded_sources'])|{'https://arxiv.org/abs/math/0211184','https://arxiv.org/abs/math/0405279','https://arxiv.org/abs/1509.03754'})
base['steering']+='\n'+den['root_r488_scope']+'\n'+den['root_cubical378413_review_scope']+'\n'+den['root_avoidable377665_review_scope']+'\n'+delta+'\n'
base.update(denials=str(denpath),year_floor=2000,candidate_pool=400,quarantined_discovery_numbers=[395,463,466,482])
spec=importlib.util.spec_from_file_location('discovery_constructor',ROOT/'prepare_discovery_packet.py');module=importlib.util.module_from_spec(spec);spec.loader.exec_module(module)
readies=[];qual='cubical-zigzag-primary-qualification-sol-r2'
for n,peer in [(490,'expanded-corpus-r491'),(491,'expanded-corpus-r490')]:
 config=json.loads(json.dumps(base));config.update(number=n,protected_peers=[qual,peer],peer_routing_files=['selection-routing-cubical-primary-qualification-r2.json']+(['selection-routing-r490.json'] if n==491 else []))
 save(ROOT/f'r{n}-config.json',config);ready=module.prepare(config);allow=read(Path(ready['lane'])/'historical-results-allowlist.json')
 for name in allow:
  rel=Path(name).relative_to(P)
  assert not any(t in part.lower() for part in rel.parts for t in forbidden)
  assert not any(part in {f'expanded-corpus-r{x}' for x in [395,463,466,482]}|{f'expanded-corpus-r{x}-parent-integration.json' for x in [395,463,466,482]} for part in rel.parts)
 readies.append(ready)
assert not set(readies[0]['ids'])&set(readies[1]['ids'])
save(ROOT/'r489-completion-boundary-delta.json',dict(utc=now,message=delta,new_protected_peers=[qual,'expanded-corpus-r490','expanded-corpus-r491'],immutable_worker_inputs_unchanged=True))
print(json.dumps(dict(files=137,frozen=13,bindings=20,receipt_exit_counts=record['receipt_exit_counts'],ready=readies,accepted_new=57,credit=0)))
