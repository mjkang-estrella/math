import os,resource
os.sched_setaffinity(0,sorted(os.sched_getaffinity(0))[:2])
resource.setrlimit(resource.RLIMIT_CPU,(120,120));resource.setrlimit(resource.RLIMIT_AS,(6*1024**3,6*1024**3))
from pathlib import Path
import json,hashlib,datetime,collections,re,importlib.util
from urllib.parse import urlsplit,unquote
P=Path(__file__).resolve().parent.parent;ROOT=P/'root-intake-r60';A=P/'expanded-corpus-r455'
def sha(q):return hashlib.sha256(q.read_bytes()).hexdigest()
def dg(b):return hashlib.sha256(b).hexdigest()
def save(q,d):
 assert not q.exists(),str(q)
 q.parent.mkdir(parents=True,exist_ok=True);q.write_text(json.dumps(d,indent=2)+'\n')
now=datetime.datetime.now(datetime.timezone.utc).isoformat();assert json.loads((P/'ledger.json').read_text())['accepted_new']==57
m=json.loads((A/'MANIFEST.json').read_text());mf=m['files'];assert len(mf)==141
routing=json.loads((ROOT/'selection-routing-r455.json').read_text());assert sha(A/'TASK.txt')==routing['task_sha256'] and sha(A/'reservation.json')==routing['reservation_sha256']
for n,v in mf.items():
 assert '..' not in Path(n).parts;q=A/n;assert not q.is_symlink() and sha(q)==v['sha256'] and q.stat().st_size==v['bytes'],n
exclusions=m['terminal_noncircular_self_exclusions'];assert {str(q.relative_to(A)) for q in A.rglob('*') if q.is_file()}==set(mf)|set(exclusions)
f=json.loads((A/'frozen-inputs.json').read_text());assert len(f)==13 and all(Path(n).parent==A and sha(Path(n))==h for n,h in f.items())
after=json.loads((A/'frozen-after.json').read_text());assert after['count']==13 and after['mismatches']==[]
rr=json.loads((A/'reservation.json').read_text());gates=json.loads((A/'results.json').read_text());prov=json.loads((A/'literal-provenance.json').read_text());assert len(rr['ids'])==20 and set(rr['ids'])==set(map(int,gates))=={v['id'] for v in prov};chunks={}
for row in prov:
 key=str(row['id']);q=Path(row['chunk']);assert q.is_relative_to(P.parent/'lanes/pi-mathdb-full-corpus-inventory-r301/corpus')
 if str(q) not in chunks:
  b=q.read_bytes();chunks[str(q)]=(dg(b),b.splitlines(keepends=True))
 h,lines=chunks[str(q)];assert h==row['chunk_sha256'];raw=lines[row['line']-1];assert dg(raw)==row['raw_line_sha256'] and row['newline'] and raw.endswith(b'\n') and (A/f'originals/{key}.jsonl').read_bytes()==raw
 obj=json.loads(raw);assert obj['mathdb_id']==row['id'];token=re.search(rb'"statement"\s*:\s*("(?:[^"\\]|\\.)*")',raw)[1]
 assert token.decode()==row['raw_statement_token'] and dg(token)==row['token_sha256'] and json.loads(token)==row['decoded_statement']==obj['statement'] and dg(obj['statement'].encode())==row['decoded_utf8_sha256']
receipts=[]
for q in sorted(A.glob('*.receipt.json')):
 v=json.loads(q.read_text());assert v['cwd']==str(A) and v['cpu_limit_s']==115 and v['as_limit_bytes']==6*1024**3 and v['deadline_s']==130
 receipts.append(dict(path=q.name,sha256=sha(q),exit=v['exit']))
assert json.loads((A/'terminal_manifest.receipt.json').read_text())['exit']==0
budget=json.loads((A/'search-budget.json').read_text());assert budget['calls_used']==2 and budget['queries_used']==6
charges=[json.loads(s) for s in (A/'search-charges.jsonl').read_text().splitlines()];assert len(charges)==2;prev=dict(calls_used=0,queries_used=0,maximum_calls=3,maximum_queries=9,charged_before_call=True)
for i,c in enumerate(charges,1):
 assert c['sequence']==i and c['before']==prev and sha(A/c['plan'])==c['plan_sha256'];assert json.loads((A/c['plan']).read_text())['queries']==c['queries'];expected=dict(prev);expected['calls_used']+=1;expected['queries_used']+=len(c['queries']);assert c['after']==expected;prev=expected;json.loads((A/f'search-response-{i}.json').read_text())
assert prev==budget and sha(A/'charge_search.py')==sha(ROOT/'charge_search.py')
events=[json.loads(s) for s in (A/'guard-ledger.jsonl').read_text().splitlines()];counts=collections.Counter(e['event'] for e in events);assert counts==dict(attempt=8,success=7,unavailable=1)
for e in events:
 if e['event']=='success':assert sha(A/e['destination'])==e['sha256']
failure=next(e for e in events if e['event']=='unavailable');assert failure['status']==403 and failure['url']=='https://www.sciencedirect.com/science/article/pii/S0095895624000996'
record=dict(utc=now,source_lane=str(A),manifest_sha256=sha(A/'MANIFEST.json'),verified_manifest_files=141,verified_original_bindings=sorted(rr['ids']),verified_frozen_bindings=13,routing_pins='Actual task and reservation hashes match retained ROOT genesis',runner_receipts=receipts,receipt_exit_counts=dict(collections.Counter(str(v['exit']) for v in receipts)),guard_events=dict(counts),search_budget=budget,search_counter_continuity='Live old/new states, exact plans/querystrings, final budget and helper hashes authenticated; both full saved responses parsed',root_disposition='ZERO_QUALIFIED_SURVIVORS_SPECIFIC336597_PRIOR_HOLD_RETAINED',ordinary_proposal=336597,scientific_summary='336597full author-only algebraic inverse-kernel proof allnonnegativeendpoints andprime-powerq retained,not independently validated; specifically named earlier Byrne-Fulcher exact-proof claim has unavailable actualbody, no authenticated exclusion or novelty clearance. Park/no formal or renewed body-retrieval lane.355749posetfiber-injection/generalquantitativecoupling unpaid;347515source noncubic theorem/integrality subcases do not pay allcubicorders.339903stronger balanced-shapeFK,330224source trimmedB-lattice and350593public loopless-coloopless matroid refutation are authenticated public/sourceown0. Remaining14 original primary bodies unread.',all20_gates=gates,process='HTTP403 preserved with real exit1/no alternate delivery; no known guard/policy/budget/cap violation reported. Material truncation recoveries, partial proof read-depth and sampled/native/writer limitations retained; no universal compliance claim.',external_manifest_inputs='Documentary external input inventories preserved, not recursively traversed; root separately verified own141files, all20 raw/token/decoded corpus bindings and frozen13.',root_scope='Integrity/provenance/routing only; no root mathematical solving/programs/Lean/checkers',credit=0,accepted_new=57,target_new=60,formal_dispatch=False,terminal_self_exclusions=exclusions)
save(P/'expanded-corpus-r455-parent-integration.json',record)
den=json.loads((ROOT/'inherited-denials-r456.json').read_text());den['utc']=now;key=urlsplit(failure['url']).hostname.lower()+unquote(urlsplit(failure['url']).path).rstrip('/')
den['blocked_keys']=sorted(set(den['blocked_keys'])|{key,'doi.org/10.1016/j.jctb.2024.12.002'})
den['blocked_artifacts']=sorted(set(den['blocked_artifacts'])|{'10.1016/j.jctb.2024.12.002','s0095895624000996','invariants of tutte partitions and a q-analogue'})
den['records'].append(dict(url=failure['url'],reason=dict(status=403,artifact='Byrne-Fulcher Invariants of Tutte partitions and a q-analogue JCTB172May2025 DOI10.1016/j.jctb.2024.12.002',restriction='Entire identified prior work unavailable ALLnew alternate host/query/version/arxiv/author/DOI/API/cache/mirror/body deliveries. Actual matching proof definitions55/57/inversion unread, no literature exclusion from snippets. Distinct original Bollen-Crapo-Jurrius1707.03459 is not denied by this different-work failure.'),evidence=dict(path=str(A/'guard-ledger.jsonl'),sha256=sha(A/'guard-ledger.jsonl'))))
den['root_r455_q_inverse_scope']='336597full author-only inverse-kernel proof retained atSPECIFICearlierexactByrne-FulcherpriorbodyHOLD; JCTB1722025DOI10.1016/j.jctb.2024.12.002/PIIS0095895624000996denied403 ALLalternate delivery unavailable,no freshretrieval/formal lane. Different original1707.03459 notsamepriorartifact.339903/330224/350593actualpublic/sourceown0;355749/347515fullscopegaps.141ownmanifest/20raw-token-decodedbindings/13frozenverified;8GEThops7payloads1denial,2search6querieslivecontinuity.'
denpath=ROOT/'inherited-denials-r457.json';save(denpath,den)
steering=json.loads((ROOT/'r456-config.json').read_text())['steering']
steering+='\nLATESTr455all0:336597ordinary all-parameterinverse-kernel algebraicproof author-only,selfchecknotindependentreview. SpecificallyidentifiedearlierexactByrne-Fulcher Invariants of Tutte partitions and a q-analogue,JCTB172May2025,DOI10.1016/j.jctb.2024.12.002/PIIS0095895624000996 actualpublisherbody403: ENTIREpriorworkALLnewalternatehost/query/version/arxiv/author/DOI/API/cache/mirror/bodydeliveriesUNAVAILABLE. No authenticatedprior-exclusionfromsnippets/no noveltyclearance. ParkatSPECIFICpriorbodyHOLD,nofreshretrieval/formallane. Different2017originalBollen-Crapo-Jurrius1707.03459 notthatdeniedwork,but target336597/1707.03459excludedfromnewinvestment.339903balancedshapeFK/330224sourcetrimmedB-lattice/350593publicloopless-colooplessmatroidrefutationzero.355749posetfiberinjection/quantitativecoupling and347515allcubicmatchingordersgap;14originalbodiesunread.8GETattempts7success1HTTP403,noalternate delivery;2search6querieslivecontinuityverified. Rootmetadata/ordinaryproposalnotnewscientificacceptance.\n'
config=dict(number=457,protected_peers=['expanded-corpus-r456','matching-ekr-source-review-sol-r1'],completed_discovery_numbers=list(range(421,456)),denials=str(denpath),excluded_ids=[326555,324571,332073,351988,338620,328748,336597],excluded_sources=['https://arxiv.org/abs/1310.5240','https://arxiv.org/abs/1211.6486','https://arxiv.org/abs/1512.05406','https://arxiv.org/abs/2109.09249','https://arxiv.org/abs/1803.02523','https://arxiv.org/abs/1409.2057','https://arxiv.org/abs/1707.03459'],peer_routing_files=['selection-routing-r456.json'],steering=steering)
save(ROOT/'r457-config.json',config);spec=importlib.util.spec_from_file_location('root_discovery_packet',ROOT/'prepare_discovery_packet.py');module=importlib.util.module_from_spec(spec);spec.loader.exec_module(module);ready=module.prepare(config)
print(json.dumps(dict(accepted_new=57,manifest_files=141,original_bindings=20,frozen_bindings=13,receipt_exit_counts=record['receipt_exit_counts'],ready=ready)))
