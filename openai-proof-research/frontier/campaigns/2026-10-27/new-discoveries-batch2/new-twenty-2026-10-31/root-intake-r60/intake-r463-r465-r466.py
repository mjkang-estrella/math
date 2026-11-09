"""Documentary-only intake. Quarantined evidence is preserved, never qualified."""
import os,resource
os.sched_setaffinity(0,sorted(os.sched_getaffinity(0))[:2])
resource.setrlimit(resource.RLIMIT_CPU,(120,120));resource.setrlimit(resource.RLIMIT_AS,(6*1024**3,6*1024**3))
from pathlib import Path
import json,hashlib,datetime,collections,re,base64
P=Path(__file__).resolve().parent.parent;ROOT=P/'root-intake-r60'
def sha(q):return hashlib.sha256(q.read_bytes()).hexdigest()
def dg(b):return hashlib.sha256(b).hexdigest()
now=datetime.datetime.now(datetime.timezone.utc).isoformat()
assert json.loads((P/'ledger.json').read_text())['accepted_new']==57
profiles=[
 dict(n=463,m='MANIFEST.json',count=184,e='terminal_noncircular_exclusions',prov='literal-bindings.json',end='manifest_final.receipt.json',q='QUARANTINE.json',get=dict(attempt=7,success=7)),
 dict(n=465,m='MANIFEST.json',count=197,e='terminal_noncircular_self_exclusions',prov='literal-provenance.json',end='final_manifest.receipt.json',q=None,get=dict(attempt=7,success=7)),
 dict(n=466,m='manifest.json',count=111,e='terminal_noncircular_exclusions',prov='original-provenance.json',end='manifest_finalize.receipt.json',q='BOUNDARY-QUARANTINE.json',get=dict(attempt=7,success=6,redirect=1))]
chunks={};out=[]
for cfg in profiles:
 n=cfg['n'];A=P/f'expanded-corpus-r{n}';routing=json.loads((ROOT/f'selection-routing-r{n}.json').read_text())
 assert sha(A/'TASK.txt')==routing['task_sha256'] and sha(A/'reservation.json')==routing['reservation_sha256']
 manifest=json.loads((A/cfg['m']).read_text());entries=manifest['files']
 if isinstance(entries,list):entries={x['path']:x for x in entries}
 assert len(entries)==cfg['count']
 for name,v in entries.items():
  assert not Path(name).is_absolute() and '..' not in Path(name).parts
  q=A/name;assert not q.is_symlink() and sha(q)==v['sha256'] and q.stat().st_size==v['bytes'],name
 exclusions=manifest[cfg['e']]
 assert {str(q.relative_to(A)) for q in A.rglob('*') if q.is_file()}==set(entries)|set(exclusions)
 frozen=json.loads((A/'frozen-inputs.json').read_text());assert len(frozen)==13 and all(Path(name).parent==A and sha(Path(name))==h for name,h in frozen.items())
 after=json.loads((A/'frozen-after.json').read_text());assert after['count']==13 and after['mismatches']==[]
 reservation=json.loads((A/'reservation.json').read_text());ids=reservation['ids'];gates=json.loads((A/'results.json').read_text());prov=json.loads((A/cfg['prov']).read_text())
 if isinstance(prov,list):prov={str(x['id']):x for x in prov}
 assert len(ids)==20 and set(ids)==set(map(int,gates))==set(map(int,prov))
 for key,row in prov.items():
  q=Path(row['chunk']);assert q.is_relative_to(P.parent/'lanes/pi-mathdb-full-corpus-inventory-r301/corpus')
  if str(q) not in chunks:
   b=q.read_bytes();chunks[str(q)]=(dg(b),b.splitlines(keepends=True))
  h,lines=chunks[str(q)];assert h==row['chunk_sha256'];raw=lines[row['line']-1]
  assert dg(raw)==row['raw_sha256'] and row['newline'] is True and raw.endswith(b'\n')
  obj=json.loads(raw);assert obj['mathdb_id']==int(key)
  token=re.search(rb'"statement"\s*:\s*("(?:[^"\\]|\\.)*")',raw)[1];decoded=obj['statement'];assert json.loads(token)==decoded
  if n==463:
   assert base64.b64decode(row['raw_base64'],validate=True)==raw and row['object']==obj and row['raw_statement_token']==token.decode() and dg(token)==row['raw_statement_token_sha256']
   assert row['decoded_statement']==decoded and dg(decoded.encode())==row['decoded_statement_sha256']
   assert (A/f'originals/{key}.jsonl').read_bytes()==raw and (A/f'originals/{key}.statement-token.json').read_bytes()==token and (A/f'originals/{key}.statement.txt').read_bytes()==decoded.encode()
   assert gates[key]['acceptance']['credit']==0
  elif n==465:
   assert row['record']==obj and dg(token)==row['token_sha256'] and dg(decoded.encode())==row['decoded_sha256']
   assert (A/f'provenance/{key}.raw.jsonl').read_bytes()==raw and (A/f'provenance/{key}.statement-token.json').read_bytes()==token and (A/f'provenance/{key}.statement.txt').read_bytes()==decoded.encode()
   assert gates[key]['literal_statement']==decoded and gates[key]['credit']==0 and not gates[key]['qualified_survivor'] and not gates[key]['formal_dispatch']
  else:
   assert base64.b64decode(row['raw_base64'],validate=True)==raw and row['record']==obj and row['statement_raw_token']==token.decode() and dg(token)==row['statement_token_sha256']
   assert row['decoded_statement']==decoded and dg(decoded.encode())==row['decoded_utf8_sha256']
 receipts=[]
 for q in sorted(A.glob('*.receipt.json')):
  v=json.loads(q.read_text());assert v['cwd']==str(A) and v['cpu_limit_s']==115 and v['as_limit_bytes']==6*1024**3 and v['deadline_s']==130
  receipts.append(dict(path=q.name,sha256=sha(q),exit=v['exit']))
 assert json.loads((A/cfg['end']).read_text())['exit']==0
 budget=json.loads((A/'search-budget.json').read_text());assert budget['calls_used']==3 and budget['queries_used']==9
 charges=[json.loads(s) for s in (A/'search-charges.jsonl').read_text().splitlines()];assert len(charges)==3
 previous=dict(calls_used=0,queries_used=0,maximum_calls=3,maximum_queries=9,charged_before_call=True)
 for i,c in enumerate(charges,1):
  assert c['sequence']==i and c['before']==previous and sha(A/c['plan'])==c['plan_sha256'] and json.loads((A/c['plan']).read_text())['queries']==c['queries']
  expected=dict(previous);expected['calls_used']+=1;expected['queries_used']+=len(c['queries']);assert c['after']==expected;previous=expected
  response_name=f"search-response-{['one','two','three'][i-1]}.json" if n==463 else f'search{i}-response.json'
  assert json.loads((A/response_name).read_text())
 assert previous==budget and sha(A/'charge_search.py')==sha(ROOT/'charge_search.py')
 events=[json.loads(s) for s in (A/'guard-ledger.jsonl').read_text().splitlines()];counts=collections.Counter(e['event'] for e in events);assert counts==cfg['get']
 for e in events:
  if e['event']=='success':assert sha(A/e['destination'])==e['sha256'] and (A/e['destination']).stat().st_size==e['bytes']
 quarantine=json.loads((A/cfg['q']).read_text()) if cfg['q'] else None
 if n==463:
  assert quarantine['status']=='PROCEDURAL_FAIL_QUARANTINE' and len(quarantine['affected_exact_files'])==2
  assert all('hat-bipartite-cycle-formal-parent-integration' in s for s in quarantine['affected_exact_files'])
  summary='FAIL_QUARANTINE: investigator opened two protected flat Hat formal parent-integration files despite oldallowlisting. All mathematical claims, K23/house proposal367685, derivations and acquisitions archived as ineligible evidence, not candidates; no new independent qualification or reuse. Networking/mathematics stopped at detection. Actual protected external files were not opened, hashed or otherwise followed by this root intake.'
 elif n==466:
  assert quarantine['status']=='FAIL_QUARANTINE' and quarantine['network_and_mathematics_stopped'] and quarantine['original_evidence_preserved'] and quarantine['no_history_repair']
  summary='FAIL_QUARANTINE: own saved inventory confirms98 reported prohibited reads, including Hat formal flat integrations and code-loop/Polynexus/crown/bunkbed bodies. Root steering prompted own-inventory-only check; research/network stopped. All outputs/acquisitions/provisional comparisons are quarantined and not candidates; full sustained task incomplete. Actual protected external paths were not opened, hashed or followed by root intake.'
 else:
  checked=json.loads((A/'history-reconciliation.json').read_text())['checked'];assert len(checked)==784 and not any('hat-bipartite' in str(x).lower() or 'hat-formal' in str(x).lower() for x in checked)
  summary='Cleanreported r465:330008author finite hub/triangleplusleaves spectralrho1/sitebond macroscopicuniquecluster derivation parked at informal finiteasymptotic/sourceconditional scope versus actuallaterlocallyfiniteinfinite theorem and specificallyunread1610.04897. No independent PASS, qualification or formal dispatch.333772actualsourceownBergeTheorem3full0;360708actualKousek2026Props5.1/6.5density5/6and3/4publicrefutationsbothclauses with full l=m1/diagonal/no-shiftbridge0.334190global2increasing bound/recursiveintervalclassification and353432equaldegree smoothfree/nonfreeincidence pair unpaid;369863literalstrictnesscorrection0 notconstantthresholdsolution. Fifteen originalsourceworks uncleared. Own saved history inventory contains noHatflatfiles; receiptfilter used/hat before opening. No broad retrospective processPASS.'
 record=dict(utc=now,source_lane=str(A),manifest_sha256=sha(A/cfg['m']),verified_manifest_files=cfg['count'],verified_original_bindings=sorted(ids),verified_frozen_bindings=13,routing_pins='Actual task and reservation hashes match retained ROOT genesis',runner_receipts=receipts,receipt_exit_counts=dict(collections.Counter(str(x['exit']) for x in receipts)),guard_events=dict(counts),search_budget=budget,search_counter_continuity='Live old/new states, exact plan digests/querystrings, final counter and immutable helper authenticated; all saved full response files parsed',root_disposition='FAIL_QUARANTINE_NO_SCIENTIFIC_REUSE' if quarantine else 'ZERO_QUALIFIED_SURVIVORS_330008_AUTHOR_PROPOSAL_PARKED',scientific_summary=summary,all20_gates=gates,quarantine=quarantine,quarantine_evidence_sha256=sha(A/cfg['q']) if quarantine else None,do_not_reuse_scientific_outputs=bool(quarantine),new_denials=False,process='Actual protected-read breach retained forquarantined packets; clean frozen hashes and completed packaging do NOT waive breach. Root only validated OWN completed evidence bytes and explicit corpus original bindings. Sampled/native/writer telemetry limitations retained. No universal compliance claim.',root_scope='Documentary integrity/provenance/routing only; no root mathematical solving/programs/Lean/checkers or following protected historical paths',credit=0,accepted_new=57,target_new=60,formal_dispatch=False,terminal_self_exclusions=exclusions)
 target=P/f'expanded-corpus-r{n}-parent-integration.json'
 if target.exists():
  old=json.loads(target.read_text());assert old['manifest_sha256']==record['manifest_sha256'] and old['verified_original_bindings']==record['verified_original_bindings'];record=old
 else:target.write_text(json.dumps(record,indent=2)+'\n')
 out.append(dict(lane=n,manifest=cfg['count'],originals=20,frozen=13,status=record['root_disposition'],receipt_exit_counts=record['receipt_exit_counts']))
print(json.dumps(dict(accepted_new=57,intakes=out,root_protected_paths_followed=False,new_preparation_helper_sha256=sha(ROOT/'prepare_discovery_packet.py'))))
