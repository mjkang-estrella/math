"""Root documentary intake and disjoint packet preparation; no mathematical work."""
import os,resource
os.sched_setaffinity(0,sorted(os.sched_getaffinity(0))[:2])
resource.setrlimit(resource.RLIMIT_CPU,(120,120))
resource.setrlimit(resource.RLIMIT_AS,(6*1024**3,6*1024**3))
from pathlib import Path
import json,hashlib,datetime,collections,re,base64,importlib.util
P=Path(__file__).resolve().parent.parent;ROOT=P/'root-intake-r60'
def sha(q):return hashlib.sha256(q.read_bytes()).hexdigest()
def dg(b):return hashlib.sha256(b).hexdigest()
def save(q,v):
 assert not q.exists(),str(q)
 q.write_text(json.dumps(v,indent=2)+'\n')
now=datetime.datetime.now(datetime.timezone.utc).isoformat()
assert json.loads((P/'ledger.json').read_text())['accepted_new']==57
chunks={};records=[]
for number,manifest_name,expected,search_calls,search_queries,get_count,terminal_name in [
 (456,'SHA256-MANIFEST.json',111,1,3,4,'final_manifest.receipt.json'),
 (457,'MANIFEST.json',139,2,6,7,'finalize_manifest.receipt.json')]:
 A=P/f'expanded-corpus-r{number}'
 routing=json.loads((ROOT/f'selection-routing-r{number}.json').read_text())
 assert sha(A/'TASK.txt')==routing['task_sha256'] and sha(A/'reservation.json')==routing['reservation_sha256']
 manifest=json.loads((A/manifest_name).read_text())
 entries=manifest['files']
 if isinstance(entries,list):entries={x['path']:x for x in entries}
 assert len(entries)==expected
 for name,v in entries.items():
  assert not Path(name).is_absolute() and '..' not in Path(name).parts
  q=A/name;assert not q.is_symlink() and sha(q)==v['sha256'] and q.stat().st_size==v['bytes'],name
 exclusions=manifest['precise_terminal_noncircular_exclusions'] if number==456 else manifest['terminal_noncircular_self_exclusions']
 assert {str(q.relative_to(A)) for q in A.rglob('*') if q.is_file()}==set(entries)|set(exclusions)
 frozen=json.loads((A/'frozen-inputs.json').read_text())
 assert len(frozen)==13 and all(Path(n).parent==A and sha(Path(n))==h for n,h in frozen.items())
 after=json.loads((A/'frozen-after.json').read_text());assert after['count']==13 and after['mismatches']==[]
 reservation=json.loads((A/'reservation.json').read_text());ids=reservation['ids']
 gates=json.loads((A/'results.json').read_text());assert len(ids)==20 and set(map(int,gates))==set(ids)
 prov=json.loads((A/('originals.json' if number==456 else 'literal-provenance.json')).read_text())
 if number==456:
  prov={str(x['id']):x for x in prov}
  originals={str(json.loads(b)['mathdb_id']):b for b in (A/'original20.jsonl').read_bytes().splitlines(keepends=True)}
 assert set(map(int,prov))==set(ids)
 for key,row in prov.items():
  q=Path(row['chunk']);assert q.is_relative_to(P.parent/'lanes/pi-mathdb-full-corpus-inventory-r301/corpus')
  if str(q) not in chunks:
   b=q.read_bytes();chunks[str(q)]=(dg(b),b.splitlines(keepends=True))
  h,lines=chunks[str(q)];assert h==row['chunk_sha256'];raw=lines[row['line']-1]
  assert dg(raw)==row['raw_sha256'] and row['newline'] and raw.endswith(b'\n')
  if number==456:assert row['raw_line'].encode()==originals[key]==raw
  else:assert base64.b64decode(row['raw_base64'],validate=True)==raw
  obj=json.loads(raw);assert obj['mathdb_id']==int(key)
  token=re.search(rb'"statement"\s*:\s*("(?:[^"\\]|\\.)*")',raw)[1]
  if number==456:
   assert token.decode()==row['statement_token'] and dg(token)==row['token_sha256']
   assert json.loads(token)==row['statement']==obj['statement'] and dg(obj['statement'].encode())==row['statement_sha256']
   assert gates[key]['literal']['statement']==obj['statement'] and gates[key]['acceptance']['credit']==0
  else:
   assert row['row']==obj and token.decode()==row['statement_raw_token'] and dg(token)==row['statement_raw_token_sha256']
   assert json.loads(token)==row['statement_utf8']==obj['statement'] and dg(obj['statement'].encode())==row['statement_utf8_sha256']
   assert gates[key]['literal_statement']==obj['statement'] and gates[key]['accepted_credit']==0
 receipts=[]
 for q in sorted(A.glob('*.receipt.json')):
  v=json.loads(q.read_text());assert v['cwd']==str(A) and v['cpu_limit_s']==115 and v['as_limit_bytes']==6*1024**3 and v['deadline_s']==130
  receipts.append(dict(path=q.name,sha256=sha(q),exit=v['exit']))
 assert json.loads((A/terminal_name).read_text())['exit']==0
 budget=json.loads((A/'search-budget.json').read_text());assert budget['calls_used']==search_calls and budget['queries_used']==search_queries
 charges=[json.loads(s) for s in (A/'search-charges.jsonl').read_text().splitlines()]
 assert len(charges)==search_calls
 previous=dict(calls_used=0,queries_used=0,maximum_calls=3,maximum_queries=9,charged_before_call=True)
 for i,c in enumerate(charges,1):
  assert c['sequence']==i and c['before']==previous and sha(A/c['plan'])==c['plan_sha256']
  assert json.loads((A/c['plan']).read_text())['queries']==c['queries']
  expected_budget=dict(previous);expected_budget['calls_used']+=1;expected_budget['queries_used']+=len(c['queries'])
  assert c['after']==expected_budget;previous=expected_budget
  response=json.loads((A/f'search-response-{i}.json').read_text());assert response
 assert previous==budget and sha(A/'charge_search.py')==sha(ROOT/'charge_search.py')
 events=[json.loads(s) for s in (A/'guard-ledger.jsonl').read_text().splitlines()]
 counts=collections.Counter(e['event'] for e in events);assert counts==dict(attempt=get_count,success=get_count)
 for e in events:
  if e['event']=='success':assert sha(A/e['destination'])==e['sha256'] and (A/e['destination']).stat().st_size==e['bytes']
 if number==456:
  summary='367030all-rectanglemod4 selected-cycle-orbit cancellation unpaid; actual BICAfinal Conjecture3.7 context read.369042arbitrary even-order redundant Cayleygenerating-set classification unpaid; independentlyderived subfamily already follows actualsourceTheorem19, zero.371370weak literal-class counterexample fails actual EVERYinduced-subgraph boundedness, source-definition correction zero; genuine pathwidth question unpaid. Seventeen selected original primary bodies unread. No independent mathematics validation or formal dispatch.'
  process='Missingfitz rendering failure preserved, changed Poppler rendering successful; large instruction/history displays recovered with full capped outputs. Sampled/native/writer peak limitations retained; no universal compliance claim.'
 else:
  summary='364237complete author-only graph-metric classification, with complete Menger theorem-as-printed to arbitrary connected source-nonempty graph bridge, zero routine adaptation. Originalv3 and final2025target read; actual1928Mengerproof not acquired, no historicalproof audit implied.358003primitive rank domination/generalKOH allocation and stronger plethysm embedding unpaid; specific analytic positivity claim actualbodyunread, positivity not automatically unimodality.357571arbitrarydegree triangle-free POSHordering/lift unpaid.357920actual2026Biane-Fang primary paysm1only; upper-ascent filtering fails lower-tree residue condition, generalm,r decomposition unpaid. Sixteen reserved originals unread; source claims363187/364300/361316 not authenticated exclusions.'
  process='Two searchresponse serialization errors (btoa/TextEncoder unavailable) retained; no extra network/counter mutation reported, full response retained in orchestration memory then saved before further research. Schema-specific full response files and live search continuity verified. Truncated outputs recovered; sampled/native/writer limitations retained. No universal compliance claim.'
 record=dict(utc=now,source_lane=str(A),manifest_sha256=sha(A/manifest_name),verified_manifest_files=len(entries),verified_original_bindings=sorted(ids),verified_frozen_bindings=13,routing_pins='Actual task and reservation hashes match retained ROOT genesis',runner_receipts=receipts,receipt_exit_counts=dict(collections.Counter(str(x['exit']) for x in receipts)),guard_events=dict(counts),search_budget=budget,search_counter_continuity='Live old/new states, exact plan digests/querystrings, final counter and immutable helper authenticated; all full response files parsed',root_disposition='ZERO_QUALIFIED_SURVIVORS',scientific_summary=summary,all20_gates=gates,process=process,root_reader_deviation='A bounded preliminary schema reader assumed dict manifest.files forr457; actual list causedAttributeError before any mutation. Changed schema-specific reader and this verifier cover actual list. No mathematical or worker artifact changed.',root_scope='Documentary integrity/provenance/routing only; no root mathematical solving/programs/Lean/checkers',external_inputs='Preserved documentary inventories not recursively traversed or historical certificate audited; explicit frozen13 and immutable20raw-token-decoded bindings separately verified',credit=0,accepted_new=57,target_new=60,formal_dispatch=False,new_denials=False,terminal_self_exclusions=exclusions)
 save(P/f'expanded-corpus-r{number}-parent-integration.json',record);records.append(record)
den=json.loads((ROOT/'inherited-denials-r458.json').read_text());den['utc']=now
den['root_completed_r456_r457']='Both documentary intakes verified, no new denials. r456111ownfiles20rawtokenbindings13frozen; mod4/Cayley fullscopegaps, pathwidthsource-definitioncorrection0. r457139ownfiles20rawtokenbindings13frozen; metricclassification complete routineMengerbridge0, Gaussian/POSH/generalrefinedTamari gaps. Actual2026Tamari companion m1onlynotgeneralm; exactanalyticpositivityclaim unreadnotunimodalityclearance. No new accepted credit,57/60.'
denpath=ROOT/'inherited-denials-r459.json';save(denpath,den)
base=json.loads((ROOT/'r458-config.json').read_text())
steering=base['steering']+'\nLATEST completed r456 and r457: neither has a qualified full-scope survivor. r456: 367030 lacks the modulo-four pairing of cycle-reversal orbits, despite actual final-source conjecture context; 369042 lacks arbitrary even-order redundant-generating-set classification; 371370 literal weak class refutation violates the source induced-subgraph definition and earns zero. r457: 364237 ordinary graph-metric classification has a COMPLETE source-Menger-to-target bridge, zero routine adaptation. Gaussian 358003 primitive-rank/unimodality proof, triangle-free POSH 357571 ordering lift, and refined greedy Tamari 357920 general-m residue-preserving recursion remain unpaid. Actual 2026 Biane-Fang paper covers m=1 only; total enumeration or upper-profile restriction does not settle the full refined target. A specific analytic positivity proof claim is unread and does not automatically imply unimodality. Neither packet supplies scientific acceptance; all source-neighbor histories retain their exact separate scopes. No new denials. Search-response serialization errors and local rendering failure are preserved without inventing guard/budget breaches. Root verified both manifests, all forty raw/token/decoded original bindings and both sets of thirteen frozen inputs; root did no mathematics.\n'
spec=importlib.util.spec_from_file_location('root_discovery_packet',ROOT/'prepare_discovery_packet.py');module=importlib.util.module_from_spec(spec);spec.loader.exec_module(module)
ready=[]
for number,active,peers in [(459,['expanded-corpus-r458','expanded-corpus-r460'],['selection-routing-r458.json']), (460,['expanded-corpus-r458','expanded-corpus-r459'],['selection-routing-r458.json','selection-routing-r459.json'])]:
 config=dict(number=number,protected_peers=active,completed_discovery_numbers=list(range(421,458)),denials=str(denpath),excluded_ids=base['excluded_ids'],excluded_sources=base['excluded_sources'],peer_routing_files=peers,steering=steering)
 save(ROOT/f'r{number}-config.json',config);ready.append(module.prepare(config))
assert not set(ready[0]['ids'])&set(ready[1]['ids'])
print(json.dumps(dict(accepted_new=57,intakes=[dict(lane=x['source_lane'],files=x['verified_manifest_files'],originals=len(x['verified_original_bindings']),frozen=x['verified_frozen_bindings'],receipt_exit_counts=x['receipt_exit_counts']) for x in records],ready=ready)))
