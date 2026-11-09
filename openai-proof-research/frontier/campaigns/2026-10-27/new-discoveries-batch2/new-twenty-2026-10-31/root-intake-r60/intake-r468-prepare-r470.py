"""Root documentary integrity/routing only, no mathematical execution."""
import os,resource
os.sched_setaffinity(0,sorted(os.sched_getaffinity(0))[:2])
resource.setrlimit(resource.RLIMIT_CPU,(120,120));resource.setrlimit(resource.RLIMIT_AS,(6*1024**3,6*1024**3))
from pathlib import Path
import json,hashlib,datetime,collections,re,base64,importlib.util
P=Path(__file__).resolve().parent.parent;ROOT=P/'root-intake-r60';A=P/'expanded-corpus-r468'
def sha(q):return hashlib.sha256(q.read_bytes()).hexdigest()
def dg(b):return hashlib.sha256(b).hexdigest()
def save(q,v):
 assert not q.exists(),str(q)
 q.write_text(json.dumps(v,indent=2)+'\n')
now=datetime.datetime.now(datetime.timezone.utc).isoformat();assert json.loads((P/'ledger.json').read_text())['accepted_new']==57
routing=json.loads((ROOT/'selection-routing-r468.json').read_text());assert sha(A/'TASK.txt')==routing['task_sha256'] and sha(A/'reservation.json')==routing['reservation_sha256']
manifest=json.loads((A/'MANIFEST.json').read_text());entries={x['path']:x for x in manifest['files']};assert len(entries)==109
for n,v in entries.items():
 assert not Path(n).is_absolute() and '..' not in Path(n).parts
 q=A/n;assert not q.is_symlink() and sha(q)==v['sha256'] and q.stat().st_size==v['bytes'],n
exclusions=manifest['terminal_noncircular_exclusions'];assert {str(q.relative_to(A)) for q in A.rglob('*') if q.is_file()}==set(entries)|set(exclusions)
frozen=json.loads((A/'frozen-inputs.json').read_text());assert len(frozen)==13 and all(Path(n).parent==A and sha(Path(n))==h for n,h in frozen.items())
after=json.loads((A/'frozen-after.json').read_text());assert after['count']==13 and after['mismatches']==[]
reservation=json.loads((A/'reservation.json').read_text());ids=reservation['ids'];gates=json.loads((A/'results.json').read_text());prov=json.loads((A/'literal-provenance.json').read_text());assert len(ids)==20 and set(ids)==set(map(int,gates))=={x['object']['mathdb_id'] for x in prov}
chunks={}
for row in prov:
 key=str(row['object']['mathdb_id']);q=Path(row['chunk']);assert q.is_relative_to(P.parent/'lanes/pi-mathdb-full-corpus-inventory-r301/corpus')
 if str(q) not in chunks:
  b=q.read_bytes();chunks[str(q)]=(dg(b),b.splitlines(keepends=True))
 h,lines=chunks[str(q)];assert h==row['chunk_sha256'];raw=lines[row['line']-1]
 assert dg(raw)==row['raw_sha256'] and row['newline']=='LF' and raw.endswith(b'\n') and base64.b64decode(row['raw_base64'],validate=True)==raw
 obj=json.loads(raw);assert obj==row['object'];token=re.search(rb'"statement"\s*:\s*("(?:[^"\\]|\\.)*")',raw)[1]
 assert base64.b64decode(row['statement_token_base64'],validate=True)==token and dg(token)==row['statement_token_sha256']
 assert json.loads(token)==obj['statement'] and dg(obj['statement'].encode())==row['decoded_sha256'] and gates[key]['literal']==obj['statement']
receipts=[]
for q in sorted(A.glob('*.receipt.json')):
 v=json.loads(q.read_text());assert v['cwd']==str(A) and v['cpu_limit_s']==115 and v['as_limit_bytes']==6*1024**3 and v['deadline_s']==130
 receipts.append(dict(path=q.name,sha256=sha(q),exit=v['exit']))
assert json.loads((A/'terminal_manifest.receipt.json').read_text())['exit']==0
budget=json.loads((A/'search-budget.json').read_text());assert budget['calls_used']==1 and budget['queries_used']==3
charges=[json.loads(s) for s in (A/'search-charges.jsonl').read_text().splitlines()];assert len(charges)==1
previous=dict(calls_used=0,queries_used=0,maximum_calls=3,maximum_queries=9,charged_before_call=True)
c=charges[0];assert c['sequence']==1 and c['before']==previous and sha(A/c['plan'])==c['plan_sha256'] and json.loads((A/c['plan']).read_text())['queries']==c['queries']
expected=dict(previous);expected['calls_used']+=1;expected['queries_used']+=len(c['queries']);assert c['after']==expected==budget and json.loads((A/'search-response1.json').read_text())
assert sha(A/'charge_search.py')==sha(ROOT/'charge_search.py')
events=[json.loads(s) for s in (A/'guard-ledger.jsonl').read_text().splitlines()];counts=collections.Counter(e['event'] for e in events);assert counts==dict(attempt=7,success=7)
for e in events:
 if e['event']=='success':assert sha(A/e['destination'])==e['sha256'] and (A/e['destination']).stat().st_size==e['bytes']
history=json.loads((A/'history-access.json').read_text());assert len(history)==767
forbidden=('formal','code-loop','polynexus','crown','bunkbed','tournament','hat-bipartite')
assert all(not any(token in part.lower() for token in forbidden) for x in history for part in Path(x['path']).relative_to(P).parts)
audit=json.loads((A/'final-audit.json').read_text());assert audit['protected_reads_in_saved_inventory']==[] and audit['failed_receipts']==[]
record=dict(utc=now,source_lane=str(A),manifest_sha256=sha(A/'MANIFEST.json'),verified_manifest_files=109,verified_original_bindings=sorted(ids),verified_frozen_bindings=13,routing_pins='Actual task and reservation hashes match retained ROOT genesis',runner_receipts=receipts,receipt_exit_counts=dict(collections.Counter(str(x['exit']) for x in receipts)),guard_events=dict(counts),search_budget=budget,search_counter_continuity='Live old/new states, exact plan digest/querystrings, final counter and immutable helper authenticated; full saved response parsed',root_disposition='ZERO_QUALIFIED_SURVIVORS_PUBLIC_AND_CORRECTION_EXCLUSIONS_RETAINED',scientific_summary='329457actualCutlerPebody1412.4595v1Th1.5 fullsourceownRollerCoaster construction0.377975actualWilliamsmath0307271v2 andCorteelmath0505031v1 normalization/Jfraction plus complete publiclypostedProbXiv coefficientproof(hostdisplayAug17,2026), authorindependentlyalgebracheckedfullformalseries/Lagrangebridgeandboundarycases0; machine-reviewlabelnotproof, no claim Corteel printedexactbinomialproduct2005 or universalpriorityaudit.376946partitionhemimetric adjacency commonresidualfouratom identity onlypropercase; arbitraryresidual/necessity/exposingfunctional unpaid.377681adjacentcdindex balancing onlylocal, arbitrarycontextnonadjacenttransfer/alternatingsumpositivity unpaid.377110unsignedEuler and322088vacuouscancellation onlycorrections0. Fiveoriginalsreviewed,fifteenunread.',all20_gates=gates,new_denials=False,history_access_audit=dict(saved_records=767,protected_component_matches=0,scope='ReadONLYsavedownaccessinventory, didnotfollowexternalpaths; correctedpreaccessfilter reported/receiptpreserved'),process='No reported local nonzero or capkill; actualrootparsed receipts. Savedfulloutputs and materialtruncation recoveries retained, no visualfigureinspection claimed. No protected paths in own767record accessaudit. Sampled/native/writer peak limits retained; no universalprocesscompliance assertion.',root_scope='Documentary integrity/provenance/routing only; no root mathematical solving/programs/Lean/checkers or protected externalpathfollow',credit=0,accepted_new=57,target_new=60,formal_dispatch=False,terminal_self_exclusions=exclusions)
save(P/'expanded-corpus-r468-parent-integration.json',record)
den=json.loads((ROOT/'inherited-denials-r469.json').read_text());den['utc']=now
den['root_r468_scope']='No newdenials.329457actualsourceownfullRollerCoaster theorem0;377975complete publiclyposted dated coefficientproof plus actualWilliamsCorteel definitions/Jfraction/fullformalseries bridge0, notmachine-labelclearance.376946commonresidualidentity notfulladjacencycriterion;377681adjacentbalancing notglobalarbitrarycontext maximizer.377110/322088corrections0.109ownmanifest20rawtokenbindings13frozenverified,7GETsuccess1search3queries. Ownsaved767historyrecordsaudit no protectedpathcomponents. No qualifiedsurvivor or credit.'
denpath=ROOT/'inherited-denials-r470.json';save(denpath,den)
base=json.loads((ROOT/'r469-config.json').read_text());steering=base['steering']+'\nLATESTr468completedzero:329457actualsource1412.4595v1Th1.5fullRollerCoastertheorem0.377975actualWilliamsmath0307271v2 andCorteelmath0505031v1 definitions/normalization/Jfraction plus complete publiclyposted ProbXiv proof(hostdisplayAug17,2026) was independentlyalgebrachecked for alln,k, including formal-power-series inversions/Lagrange/boundaries; public0, machine-reviewlabels are not evidence, no claim Corteel printed the exact product in2005.376946fouratom partition-cone nonadjacency identity requires identicalresidualblocks anddoesnot pay generalcriterion/necessity;377681adjacentcdindex smoothing stops at local staircase, arbitrary-context nonadjacent transfer remains unpaid.377110unsignedEuler and322088vacuoussigncancellation are corrections0. Fiveassignedoriginalsread,fifteenunread. Own767savedhistoryaccessrecords have no protectedcomponents, no externalpathfollow byROOT.7GETsuccess/1search3queries,no newdenials;109ownfiles20originalbindings13frozenverified,57/60unchanged.\n'
config=dict(base);config.update(number=470,protected_peers=['expanded-corpus-r467','expanded-corpus-r469'],peer_routing_files=['selection-routing-r467.json','selection-routing-r469.json'],completed_discovery_numbers=sorted(set(base['completed_discovery_numbers'])|{468}),denials=str(denpath),steering=steering,year_floor=2000,candidate_pool=400)
save(ROOT/'r470-config.json',config)
spec=importlib.util.spec_from_file_location('root_discovery_packet',ROOT/'prepare_discovery_packet.py');module=importlib.util.module_from_spec(spec);spec.loader.exec_module(module);ready=module.prepare(config)
allow=json.loads((Path(ready['lane'])/'historical-results-allowlist.json').read_text());assert all(not any(token in part.lower() for token in forbidden) for name in allow for part in Path(name).relative_to(P).parts)
assert all('expanded-corpus-r463' not in name and 'expanded-corpus-r466' not in name for name in allow)
print(json.dumps(dict(accepted_new=57,manifest_files=109,original_bindings=20,frozen_bindings=13,receipt_exit_counts=record['receipt_exit_counts'],new_denials=False,ready=ready,history_filter='Actualallowlist andcompletedownaccessinventory contain no protected pathcomponent')))
