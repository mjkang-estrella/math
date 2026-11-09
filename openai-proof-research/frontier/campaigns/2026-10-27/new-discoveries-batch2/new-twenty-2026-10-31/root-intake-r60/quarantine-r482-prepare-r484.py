"""Root forensic integrity only; never reuse quarantined scientific outputs."""
import os,resource
os.sched_setaffinity(0,sorted(os.sched_getaffinity(0))[:2]);resource.setrlimit(resource.RLIMIT_CPU,(120,120));resource.setrlimit(resource.RLIMIT_AS,(6*1024**3,6*1024**3))
from pathlib import Path
import json,hashlib,datetime,collections,re,importlib.util
P=Path(__file__).resolve().parent.parent;ROOT=P/'root-intake-r60';A=P/'expanded-corpus-r482'
def sha(q):return hashlib.sha256(q.read_bytes()).hexdigest()
def dg(b):return hashlib.sha256(b).hexdigest()
def save(q,v):
 assert not q.exists(),str(q)
 q.write_text(json.dumps(v,indent=2)+'\n')
now=datetime.datetime.now(datetime.timezone.utc).isoformat();assert json.loads((P/'ledger.json').read_text())['accepted_new']==57
route=json.loads((ROOT/'selection-routing-r482.json').read_text());assert sha(A/'TASK.txt')==route['task_sha256'] and sha(A/'reservation.json')==route['reservation_sha256']
m=json.loads((A/'SHA256SUMS.json').read_text());entries={x['path']:x for x in m['files']};assert len(entries)==len(m['files'])==153
for n,v in entries.items():
 assert not Path(n).is_absolute() and '..' not in Path(n).parts
 q=A/n;assert not q.is_symlink() and sha(q)==v['sha256'] and q.stat().st_size==v['bytes'],n
exclusions=m['excluded'];assert set(exclusions)=={'SHA256SUMS.json','manifest_finalize.receipt.json','manifest_finalize.output.txt'}
assert {str(q.relative_to(A)) for q in A.rglob('*') if q.is_file()}==set(entries)|set(exclusions)
frozen=json.loads((A/'frozen-inputs.json').read_text());assert len(frozen)==13 and all(Path(n).parent==A and sha(Path(n))==h for n,h in frozen.items())
after=json.loads((A/'frozen-after.json').read_text());assert after['count']==13 and after['mismatches']==[]
prov=json.loads((A/'original-provenance.json').read_text());ids=json.loads((A/'reservation.json').read_text())['ids'];assert len(ids)==len(prov)==20 and set(ids)=={v['id'] for v in prov}==set(route['ids'])
chunks={}
for row in prov:
 q=Path(row['chunk']);assert q.is_relative_to(P.parent/'lanes/pi-mathdb-full-corpus-inventory-r301/corpus')
 if str(q) not in chunks:
  b=q.read_bytes();chunks[str(q)]=(dg(b),b.splitlines(keepends=True))
 h,lines=chunks[str(q)];assert h==row['chunk_sha256'];raw=lines[row['line']-1];obj=json.loads(raw)
 assert row['newline'] is True and raw.endswith(b'\n') and dg(raw)==row['raw_sha256'] and obj['mathdb_id']==row['id'] and (A/'originals'/f"{row['id']}.jsonl").read_bytes()==raw
 token=re.search(rb'"statement"\s*:\s*("(?:[^"\\]|\\.)*")',raw)[1];assert row['statement_key']=='statement' and dg(token)==row['token_sha256'] and json.loads(token)==obj['statement'] and dg(obj['statement'].encode())==row['decoded_sha256']
receipts=[]
for q in sorted(A.glob('*.receipt.json')):
 v=json.loads(q.read_text());assert v['cwd']==str(A) and v['cpu_limit_s']==115 and v['as_limit_bytes']==6*1024**3 and v['deadline_s']==130
 receipts.append(dict(path=q.name,sha256=sha(q),exit=v['exit']))
assert json.loads((A/'manifest_finalize.receipt.json').read_text())['exit']==0
budget=json.loads((A/'search-budget.json').read_text());assert budget==dict(calls_used=2,queries_used=6,maximum_calls=3,maximum_queries=9,charged_before_call=True)
charges=[json.loads(s) for s in (A/'search-charges.jsonl').read_text().splitlines()];assert len(charges)==2
prev=dict(calls_used=0,queries_used=0,maximum_calls=3,maximum_queries=9,charged_before_call=True)
for i,c in enumerate(charges,1):
 assert c['sequence']==i and c['before']==prev and sha(A/c['plan'])==c['plan_sha256'] and json.loads((A/c['plan']).read_text())['queries']==c['queries']
 nxt=dict(prev);nxt['calls_used']+=1;nxt['queries_used']+=len(c['queries']);assert c['after']==nxt;prev=nxt
 assert json.loads((A/f'search{i}-response.json').read_text())
assert prev==budget and sha(A/'charge_search.py')==sha(ROOT/'charge_search.py')
events=[json.loads(s) for s in (A/'guard-ledger.jsonl').read_text().splitlines()];counts=collections.Counter(e['event'] for e in events);assert counts==dict(attempt=6,success=6)
for e in events:
 if e['event']=='success':assert sha(A/e['destination'])==e['sha256'] and (A/e['destination']).stat().st_size==e['bytes']
failure=json.loads((A/'PROCEDURAL-FAIL-QUARANTINE.json').read_text());assert failure['status']=='FAIL_QUARANTINE' and failure['eligible_outputs'] is False and failure['network_after_trigger']==0
assert '/server/api/' in failure['url'] and events[-1]['event']=='success' and events[-1]['url']==failure['url'] and events[-1]['status']==200
history=json.loads((A/'history-access.json').read_text());assert len(history)==798;forbidden=('formal','code-loop','code_loop','polynexus','crown','bunkbed','tournament','hat-bipartite')
assert all(not any(t in part.lower() for t in forbidden) for x in history for part in Path(x['path']).relative_to(P).parts)
assert all(not any(f'expanded-corpus-r{n}' in x['path'] for n in [395,463,466]) for x in history)
record=dict(utc=now,source_lane=str(A),task_reservation_genesis_verified=True,manifest_sha256=sha(A/'SHA256SUMS.json'),verified_manifest_files=153,verified_original_bindings=sorted(ids),verified_frozen_bindings=13,runner_receipts=receipts,receipt_exit_counts=dict(collections.Counter(str(x['exit']) for x in receipts)),guard_events=dict(counts),search_budget=budget,root_disposition='FAIL_QUARANTINE_ENTIRE_PACKET',failure=failure,failure_sha256=sha(A/'PROCEDURAL-FAIL-QUARANTINE.json'),
 root_adjudication='Forbiddenrepository/server/api/documentGETis an actual API restriction breach even though public/noaccount/transport200/guardaccepted. Entirepacketoutputs/acquisitions/claimsINELIGIBLE,no candidates,proofreuse,sourceacquisitionseed/refetch,formaldispatch orcredit. Frozenhashesclean doNOTwaive breach. HTTPsuccessrowunchanged,no invented denial or arbitrary blanketban all papers fromthesehosts.',
 root_read_scope='Forensicownmanifest/payloadhashes,receipts,provenance,accessmetadata andbreachbriefonly. No scientificsourcebody/extractedproof/resultsgates/QUARANTINED-ATTEMPTS read for mathematical reuse. Incidentally visible claims in breachbrief not routed or adopted.',
 root_scope='Documentaryintegrity/accessadjudication only,no root mathematical solving/programs/Lean/checkers.',do_not_reuse_scientific_outputs=True,do_not_reuse_source_acquisitions_or_seeds=True,reservation_remains_occupied=True,credit=0,accepted_new=57,target_new=60,formal_dispatch=False,terminal_self_exclusions=exclusions)
save(P/'expanded-corpus-r482-parent-integration.json',record)
den=json.loads((ROOT/'inherited-denials-r486.json').read_text());den['utc']=now
delta='ROOTQUARANTINEr482ENTIREpacket: forbiddenpublicrepository /server/api/core/bitstreams/.../contentGET violatedexplicitNOAPIinstruction despiteguardaccepted/transport200. ALLr482outputs/acquisitions/claims permanentlyINELIGIBLE,no read/reuse/candidate/primaryseed/refetch/historyintegration. Its20reservationsremainoccupied. Clean13frozenhashesDONOTcurebreach. No actualHTTPdenialorblanketdenialofeveryunderlyingoriginalworkinferred;guardhistoryunchanged. SourceURLswith /server/api/ are APIs even ifcontentendsinPDF/directdocumentroute; inspectplanURL BEFORE GET,no guardacceptanceaspolicypermission. Futurehistoryfilter excludesr482directoryANDflatparentintegration BEFOREstat/open/hash,alongwithr395/r463/r466. Rootforensicverified153ownfiles20originalbindings13frozen6transport200GET2search6queries798savedhistorypaths,notmathematicalclearance. No candidate/credit;57/60unchanged.'
den['root_r482_quarantine']=delta;denpath=ROOT/'inherited-denials-r487.json';save(denpath,den)
config=json.loads((ROOT/'r483-config.json').read_text());config.update(number=484,protected_peers=['expanded-corpus-r483','eps-zero-weight-source-review-sol-r1'],peer_routing_files=['selection-routing-r483.json','selection-routing-eps-review-r1.json'],denials=str(denpath),steering=config['steering']+'\n'+delta+'\n',year_floor=2000,candidate_pool=400)
config['quarantined_discovery_numbers']=sorted(set(config.get('quarantined_discovery_numbers',[]))|{395,463,466,482})
config['excluded_ids']=sorted(set(config['excluded_ids'])|set(route['ids']));config['excluded_sources']=sorted(set(config['excluded_sources'])|set(route['sources']))
save(ROOT/'r484-config.json',config)
spec=importlib.util.spec_from_file_location('root_discovery_packet',ROOT/'prepare_discovery_packet.py');module=importlib.util.module_from_spec(spec);spec.loader.exec_module(module);ready=module.prepare(config)
allow=json.loads((Path(ready['lane'])/'historical-results-allowlist.json').read_text())
assert all(not any(t in part.lower() for t in forbidden) for n in allow for part in Path(n).relative_to(P).parts)
assert all(not any(f'expanded-corpus-r{n}' in x for n in [395,463,466,482]) for x in allow)
save(ROOT/'r482-quarantine-boundary-delta.json',dict(utc=now,message=delta,new_protected_peer='expanded-corpus-r484',immutable_worker_inputs_unchanged=True))
print(json.dumps(dict(manifest_files=153,original_bindings=20,frozen_bindings=13,root_disposition=record['root_disposition'],receipt_exit_counts=record['receipt_exit_counts'],ready=ready)))
