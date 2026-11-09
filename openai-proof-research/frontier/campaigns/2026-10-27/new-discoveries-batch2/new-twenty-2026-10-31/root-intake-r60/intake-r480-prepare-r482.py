"""Root documentary intake and disjoint metadata routing; no mathematics."""
import os,resource
os.sched_setaffinity(0,sorted(os.sched_getaffinity(0))[:2]);resource.setrlimit(resource.RLIMIT_CPU,(120,120));resource.setrlimit(resource.RLIMIT_AS,(6*1024**3,6*1024**3))
from pathlib import Path
import json,hashlib,datetime,collections,re,importlib.util
P=Path(__file__).resolve().parent.parent;ROOT=P/'root-intake-r60';A=P/'expanded-corpus-r480'
def sha(q):return hashlib.sha256(q.read_bytes()).hexdigest()
def dg(b):return hashlib.sha256(b).hexdigest()
def save(q,v):
 assert not q.exists(),str(q)
 q.write_text(json.dumps(v,indent=2)+'\n')
now=datetime.datetime.now(datetime.timezone.utc).isoformat();assert json.loads((P/'ledger.json').read_text())['accepted_new']==57
route=json.loads((ROOT/'selection-routing-r480.json').read_text());assert sha(A/'TASK.txt')==route['task_sha256'] and sha(A/'reservation.json')==route['reservation_sha256']
m=json.loads((A/'SHA256SUMS.json').read_text());entries=m['files'];assert len(entries)==134
for n,v in entries.items():
 assert not Path(n).is_absolute() and '..' not in Path(n).parts
 q=A/n;assert not q.is_symlink() and sha(q)==v['sha256'] and q.stat().st_size==v['bytes'],n
exclusions=m['terminal_noncircular_self_exclusions'];assert set(exclusions)=={'SHA256SUMS.json','terminal_manifest.receipt.json','terminal_manifest.output.txt'}
assert {str(q.relative_to(A)) for q in A.rglob('*') if q.is_file()}==set(entries)|set(exclusions)
frozen=json.loads((A/'frozen-inputs.json').read_text());assert len(frozen)==13 and all(Path(n).parent==A and sha(Path(n))==h for n,h in frozen.items())
after=json.loads((A/'frozen-after.json').read_text());assert after['count']==13 and after['mismatches']==[]
prov=json.loads((A/'provenance.json').read_text());gates=json.loads((A/'results.json').read_text());ids=json.loads((A/'reservation.json').read_text())['ids'];assert len(ids)==len(prov)==20 and set(ids)==set(map(int,gates))==set(map(int,prov))
chunks={};sources={}
for key,row in prov.items():
 q=Path(row['chunk']);assert q.is_relative_to(P.parent/'lanes/pi-mathdb-full-corpus-inventory-r301/corpus')
 if str(q) not in chunks:
  b=q.read_bytes();chunks[str(q)]=(dg(b),b.splitlines(keepends=True))
 h,lines=chunks[str(q)];assert h==row['chunk_sha256'];raw=lines[row['line_1based']-1];obj=json.loads(raw)
 assert row['newline'] is True and raw.endswith(b'\n') and dg(raw)==row['raw_sha256'] and obj['mathdb_id']==int(key) and (A/'originals'/f'{key}.jsonl').read_bytes()==raw
 token=re.search(rb'"statement"\s*:\s*("(?:[^"\\]|\\.)*")',raw)[1]
 assert token.decode()==row['statement_token'] and dg(token)==row['statement_token_sha256'] and json.loads(token)==row['statement']==obj['statement']==gates[key]['literal_gate']['statement'] and dg(obj['statement'].encode())==row['statement_utf8_sha256']
 assert row['raw_line_path']==f'originals/{key}.jsonl'
 sources[key]=obj['source_url']
receipts=[]
for q in sorted(A.glob('*.receipt.json')):
 v=json.loads(q.read_text());assert v['cwd']==str(A) and v['cpu_limit_s']==115 and v['as_limit_bytes']==6*1024**3 and v['deadline_s']==130
 receipts.append(dict(path=q.name,sha256=sha(q),exit=v['exit']))
assert json.loads((A/'terminal_manifest.receipt.json').read_text())['exit']==0
budget=json.loads((A/'search-budget.json').read_text());assert budget==dict(calls_used=3,queries_used=9,maximum_calls=3,maximum_queries=9,charged_before_call=True)
charges=[json.loads(s) for s in (A/'search-charges.jsonl').read_text().splitlines()];assert len(charges)==3
prev=dict(calls_used=0,queries_used=0,maximum_calls=3,maximum_queries=9,charged_before_call=True)
for i,c in enumerate(charges,1):
 assert c['sequence']==i and c['before']==prev and sha(A/c['plan'])==c['plan_sha256'] and json.loads((A/c['plan']).read_text())['queries']==c['queries']
 nxt=dict(prev);nxt['calls_used']+=1;nxt['queries_used']+=len(c['queries']);assert c['after']==nxt;prev=nxt
 assert isinstance(json.loads((A/f'search{i}-response.json').read_text()),str)
assert prev==budget and sha(A/'charge_search.py')==sha(ROOT/'charge_search.py')
events=[json.loads(s) for s in (A/'guard-ledger.jsonl').read_text().splitlines()];counts=collections.Counter(e['event'] for e in events);assert counts==dict(attempt=8,success=8)
for e in events:
 if e['event']=='success':assert sha(A/e['destination'])==e['sha256'] and (A/e['destination']).stat().st_size==e['bytes']
history=json.loads((A/'history-access.json').read_text());assert len(history)==794;forbidden=('formal','code-loop','code_loop','polynexus','crown','bunkbed','tournament','hat-bipartite')
assert all(not any(t in part.lower() for t in forbidden) for x in history for part in Path(x['path']).relative_to(P).parts)
assert all(not any(f'expanded-corpus-r{n}' in x['path'] for n in [395,463,466]) for x in history)
summary='322552actual1111.3513v2/final2014retainsunicyclicEVERYspanningtreepartitiondimensionconjecture;outside-distancecutoffandroot-heightoffsetsdefeatnaivesingletonrefinement,full+1lemma unpaid.322416actualOSullivanTh7.3polynomiality/monicity/roots0,1publicnotall-rconvexity/alternation;fixedr1/r2sourceknown0,principal-subsumlossconvexitynotcounterexampleforfullP_r,uniformsigncertificateunpaid.319715actualLevande1006.3013Claim6.1fullinsertion/indexreversalrecurrenceexactpublic0.322380sourceimmediatefreenesstruthannouncement0,underlyingmonoidnotfullcategoricalHopfproof.320140actualBessenrodtTewariVanWilligenburgTh5.5upper-shaperectangleclassificationpublic0,lowerLRdependenciesattributednotfullyaudited.320174specificYoungproofclaimbodyHOLD.'
record=dict(utc=now,source_lane=str(A),task_reservation_genesis_verified=True,manifest_sha256=sha(A/'SHA256SUMS.json'),verified_manifest_files=134,verified_original_bindings=sorted(ids),verified_frozen_bindings=13,source_url_by_id=sources,all20_gates=gates,runner_receipts=receipts,receipt_exit_counts=dict(collections.Counter(str(x['exit']) for x in receipts)),guard_events=dict(counts),search_budget=budget,search_counter_continuity='Three live before/afterstates,exactplans/querystrings,immutablehelper andfullsavedJSON-stringresponsesverified.',root_disposition='ZERO_QUALIFIED_SURVIVORS',scientific_summary=summary,
 reading_limits='Fourassignedoriginalsread,sixteenunread,fourfollowup/finalcomparisons,novisualfigureaudit,nofullLRdependency audit.',
 process='794savedhistoricalpathsnamechecked,norootprotectedexternalpathfollow.372884bytecountmatchnoise,notdisposition.8PDFGETsuccess3search9queries,nonewdenials/failedcommands. Materialsourcepassagesrecovered,native/transient/writerpeaksunknown,nouniversalcomplianceclaim.',root_intake_repair='Read-only derivative-builder first stopped before file writes because manifest filename occurs twice; exact expected multiplicity corrected,worker evidence unchanged.',root_scope='Documentaryprovenance/integrity/routingonly,norootmathematics/programs/Lean/checkers.',credit=0,accepted_new=57,target_new=60,formal_dispatch=False,terminal_self_exclusions=exclusions)
save(P/'expanded-corpus-r480-parent-integration.json',record)
den=json.loads((ROOT/'inherited-denials-r483.json').read_text());den['utc']=now
delta='Completedr480zeroqualifiedsurvivors. '+summary+'134ownfiles20raw/token/decodedbindings13frozen794savedhistorypathsverified,8PDFGETsuccess3search9queries,nonewdenials/credit/dispatch.57/60unchanged.'
den['root_r480_scope']=delta;denpath=ROOT/'inherited-denials-r484.json';save(denpath,den)
config=json.loads((ROOT/'r481-config.json').read_text());config.update(number=482,protected_peers=['expanded-corpus-r479','expanded-corpus-r481'],peer_routing_files=['selection-routing-r479.json','selection-routing-r481.json'],completed_discovery_numbers=sorted(set(config['completed_discovery_numbers'])|{480}),denials=str(denpath),steering=config['steering']+'\n'+delta+'\n',year_floor=2000,candidate_pool=400)
save(ROOT/'r482-config.json',config)
spec=importlib.util.spec_from_file_location('root_discovery_packet',ROOT/'prepare_discovery_packet.py');module=importlib.util.module_from_spec(spec);spec.loader.exec_module(module);ready=module.prepare(config)
allow=json.loads((Path(ready['lane'])/'historical-results-allowlist.json').read_text())
assert all(not any(t in part.lower() for t in forbidden) for n in allow for part in Path(n).relative_to(P).parts)
assert all(not any(f'expanded-corpus-r{n}' in x for n in [395,463,466]) for x in allow)
save(ROOT/'r480-completion-boundary-delta.json',dict(utc=now,message=delta,new_protected_peer='expanded-corpus-r482',immutable_worker_inputs_unchanged=True))
print(json.dumps(dict(manifest_files=134,frozen_bindings=13,original_bindings=20,receipt_exit_counts=record['receipt_exit_counts'],ready=ready)))
