"""Root documentary verification and discovery routing only."""
import os,resource
os.sched_setaffinity(0,sorted(os.sched_getaffinity(0))[:2])
resource.setrlimit(resource.RLIMIT_CPU,(120,120));resource.setrlimit(resource.RLIMIT_AS,(6*1024**3,6*1024**3))
from pathlib import Path
import json,hashlib,datetime,collections,re,base64,importlib.util
from urllib.parse import urlsplit,unquote
P=Path(__file__).resolve().parent.parent;ROOT=P/'root-intake-r60';A=P/'expanded-corpus-r459'
def sha(q):return hashlib.sha256(q.read_bytes()).hexdigest()
def dg(b):return hashlib.sha256(b).hexdigest()
def save(q,v):
 assert not q.exists(),str(q)
 q.write_text(json.dumps(v,indent=2)+'\n')
now=datetime.datetime.now(datetime.timezone.utc).isoformat()
assert json.loads((P/'ledger.json').read_text())['accepted_new']==57
routing=json.loads((ROOT/'selection-routing-r459.json').read_text())
assert sha(A/'TASK.txt')==routing['task_sha256'] and sha(A/'reservation.json')==routing['reservation_sha256']
manifest=json.loads((A/'MANIFEST.json').read_text());entries={x['path']:x for x in manifest['files']};assert len(entries)==143
for n,v in entries.items():
 assert not Path(n).is_absolute() and '..' not in Path(n).parts
 q=A/n;assert not q.is_symlink() and sha(q)==v['sha256'] and q.stat().st_size==v['bytes'],n
exclusions=manifest['terminal_noncircular_exclusions']
assert {str(q.relative_to(A)) for q in A.rglob('*') if q.is_file()}==set(entries)|set(exclusions)
frozen=json.loads((A/'frozen-inputs.json').read_text());assert len(frozen)==13 and all(Path(n).parent==A and sha(Path(n))==h for n,h in frozen.items())
after=json.loads((A/'frozen-after.json').read_text());assert after['count']==13 and after['mismatches']==[]
reservation=json.loads((A/'reservation.json').read_text());ids=reservation['ids'];gates=json.loads((A/'results.json').read_text());prov=json.loads((A/'provenance.json').read_text())
assert len(ids)==20 and set(ids)==set(map(int,gates))==set(map(int,prov))
chunks={}
for key,row in prov.items():
 q=Path(row['chunk']);assert q.is_relative_to(P.parent/'lanes/pi-mathdb-full-corpus-inventory-r301/corpus')
 if str(q) not in chunks:
  b=q.read_bytes();chunks[str(q)]=(dg(b),b.splitlines(keepends=True))
 h,lines=chunks[str(q)];assert h==row['chunk_sha256'];raw=lines[row['line']-1]
 assert dg(raw)==row['raw_sha256'] and row['newline'] and raw.endswith(b'\n') and (A/f'originals/{key}.jsonl').read_bytes()==base64.b64decode(row['raw_base64'],validate=True)==raw
 obj=json.loads(raw);assert obj['mathdb_id']==int(key)
 token=re.search(rb'"statement"\s*:\s*("(?:[^"\\]|\\.)*")',raw)[1]
 assert base64.b64decode(row['token_base64'],validate=True)==token and dg(token)==row['token_sha256']
 assert json.loads(token)==obj['statement'] and dg(obj['statement'].encode())==row['decoded_sha256']
 assert gates[key]['literal']['statement']==obj['statement'] and gates[key]['acceptance']['credit']==0
receipts=[]
for q in sorted(A.glob('*.receipt.json')):
 v=json.loads(q.read_text());assert v['cwd']==str(A) and v['cpu_limit_s']==115 and v['as_limit_bytes']==6*1024**3 and v['deadline_s']==130
 receipts.append(dict(path=q.name,sha256=sha(q),exit=v['exit']))
assert json.loads((A/'terminal_manifest.receipt.json').read_text())['exit']==0
budget=json.loads((A/'search-budget.json').read_text());assert budget['calls_used']==2 and budget['queries_used']==6
charges=[json.loads(s) for s in (A/'search-charges.jsonl').read_text().splitlines()];assert len(charges)==2
previous=dict(calls_used=0,queries_used=0,maximum_calls=3,maximum_queries=9,charged_before_call=True)
for i,c in enumerate(charges,1):
 assert c['sequence']==i and c['before']==previous and sha(A/c['plan'])==c['plan_sha256']
 assert json.loads((A/c['plan']).read_text())['queries']==c['queries']
 expected=dict(previous);expected['calls_used']+=1;expected['queries_used']+=len(c['queries']);assert c['after']==expected;previous=expected
 response=json.loads((A/f'search-response-{i}.json').read_text());assert response
assert previous==budget and sha(A/'charge_search.py')==sha(ROOT/'charge_search.py')
events=[json.loads(s) for s in (A/'guard-ledger.jsonl').read_text().splitlines()];counts=collections.Counter(e['event'] for e in events);assert counts==dict(attempt=4,success=3,unavailable=1)
for e in events:
 if e['event']=='success':assert sha(A/e['destination'])==e['sha256'] and (A/e['destination']).stat().st_size==e['bytes']
failure=next(e for e in events if e['event']=='unavailable');assert failure['status']==404 and failure['url']=='https://arxiv.org/pdf/2004.05544'
plan=json.loads((A/'get-plan-4.json').read_text());assert plan['url']==failure['url'] and plan['routes']==['346667']
record=dict(utc=now,source_lane=str(A),manifest_sha256=sha(A/'MANIFEST.json'),verified_manifest_files=143,verified_original_bindings=sorted(ids),verified_frozen_bindings=13,routing_pins='Actual task and reservation hashes match retained ROOT genesis',runner_receipts=receipts,receipt_exit_counts=dict(collections.Counter(str(x['exit']) for x in receipts)),guard_events=dict(counts),search_budget=budget,search_counter_continuity='Live old/new states, exact plan digests/querystrings, final counter and immutable helper authenticated; both full saved response files parsed',root_disposition='ZERO_QUALIFIED_SURVIVORS',scientific_summary='351065convex grabbing redred exchange conditionalinduction doesnot pay redversusgreen minimax comparison or paritydebt; fullsourcequestionunpaid.346667integral objectwise commutator generation doesnot pay categoricaltensor bounded-support generation/commonminor factorization/componentbasepoint conventions; specificallycitedMPR2004.05544actualbody404unavailable.348334LCsuccessor genericdeBruijn theorem doesnot pay exactFredricksenKessler1977construction, splicecriterion/orderedcycletree/periodicties unpaid. Seventeen reserved primary bodies unread.341720conditionalGoldbergSeymour densitybridge retained, actualprimaryproofunreadnotauthenticated exclusion; source/endpoint corrections0. No fullscopeordinary endpoint or candidate submitted.',all20_gates=gates,new_denial=dict(work='Cited Miyata-Proudfoot-Ramos categorical graph-minor work identified as2004.05544; actualbodyunread',event=failure,plan=plan,scope='ENTIREidentifiedwork ALLnewalternate host/query/version/arxiv/author/cache/mirror/DOI/API/body/metadata deliveries unavailable. Distinct acquired AgrawalBanksGadishMiyata2005.13666original is not denied by this different-work failure. No retry or indirect recovery.'),process='Preserved get_mpr exit1 HTTP404, no retry/alternate delivery or accesspolicy/budget rejection reported. Large saved literal/denial/history outputs recovered at relevant bounded passages. No figures visually inspected; no sourcefigure counterexample certified. Sampled/native/writer peak limits retained; no universal processcompliance claim.',root_scope='Documentary integrity/provenance/routing only; no root mathematical solving/programs/Lean/checkers',external_inputs='Preserved documentary inventories not recursively traversed or historical certificate audited; explicit frozen13 and immutable20raw-token-decoded bindings separately verified',credit=0,accepted_new=57,target_new=60,formal_dispatch=False,terminal_self_exclusions=exclusions)
save(P/'expanded-corpus-r459-parent-integration.json',record)
den=json.loads((ROOT/'inherited-denials-r461.json').read_text());den['utc']=now
den['blocked_keys']=sorted(set(den['blocked_keys'])|{urlsplit(failure['url']).hostname.lower()+unquote(urlsplit(failure['url']).path).rstrip('/')})
den['blocked_artifacts']=sorted(set(den['blocked_artifacts'])|{'2004.05544'})
den['records'].append(dict(url=failure['url'],reason=dict(status=404,artifact='CitedMiyataProudfootRamos categorical graphminor work2004.05544',restriction='Entireidentifiedwork ALLnewalternate host/query/version/arxiv/author/cache/mirror/DOI/API/body/metadata deliveries unavailable. Actual cited tensor/principal-module theorem/proof unread. Do not correct presumed arxiv identity by alternate lookup/delivery afterfailure. Distinct acquired original AgrawalBanksGadishMiyata2005.13666 notsamefailedwork.'),evidence=dict(path=str(A/'guard-ledger.jsonl'),sha256=sha(A/'guard-ledger.jsonl'),plan=str(A/'get-plan-4.json'),plan_sha256=sha(A/'get-plan-4.json'))))
den['root_r459_scope']='351065redgreen minimax/paritydebt gap;346667objectwiseintegralLie generation notcategoricaltensorbounded support and citedMPR2004.05544body404wholeworkallnewdeliveryunavailable;348334actual1977algorithm/splice/cycletree/periodictie bridge unpaid.143ownmanifest20rawtokenbindings13frozenverified,4GETattempts3payloads1HTTP404,2search6queries. No qualifiedsurvivor or credit.'
denpath=ROOT/'inherited-denials-r462.json';save(denpath,den)
base=json.loads((ROOT/'r461-config.json').read_text())
steering=base['steering']+'\nLATEST completed r459 has no full-scope ordinary endpoint or qualified survivor. 351065 red-red exchange conditional induction does not establish the necessary red-versus-green minimax inequality; strategy-stealing turn parity and score debt remain unpaid. 346667 natural integral commutator generation is objectwise, not categorical finite generation of tensor powers; common-support/minor factorization and exact component/basepoint conventions remain unpaid. The cited Miyata-Proudfoot-Ramos graph-minor work identified as arXiv2004.05544 returned HTTP404. ENTIRE identified work is unavailable for ALL new hosts, versions, arXiv, author copies, mirrors, caches, DOI/API/body/metadata deliveries; no retry, alternate lookup to correct identity, or indirect recovery. Its actual theorem/proof remains unread. Distinct acquired Agrawal-Banks-Gadish-Miyata original2005.13666 is not denied by this different-work failure. 348334 generic LC deBruijn successor theorem does not pay equality with specifically unread Fredricksen-Kessler1977 lex-composition construction; exact splice set, ordered cycle tree and periodic/complement tie bridges unpaid. Seventeen reserved original bodies unread. 341720 has a conditional Goldberg-Seymour density bridge, not an authenticated actual-primary-proof exclusion. Root verified143 ownfiles,20original bindings,13frozen inputs; no new mathematical validation or credit.\n'
config=dict(number=462,protected_peers=['expanded-corpus-r460','expanded-corpus-r461'],completed_discovery_numbers=list(range(421,460)),denials=str(denpath),excluded_ids=base['excluded_ids'],excluded_sources=base['excluded_sources'],peer_routing_files=['selection-routing-r460.json','selection-routing-r461.json'],steering=steering)
save(ROOT/'r462-config.json',config)
spec=importlib.util.spec_from_file_location('root_discovery_packet',ROOT/'prepare_discovery_packet.py');module=importlib.util.module_from_spec(spec);spec.loader.exec_module(module);ready=module.prepare(config)
print(json.dumps(dict(accepted_new=57,manifest_files=143,original_bindings=20,frozen_bindings=13,receipt_exit_counts=record['receipt_exit_counts'],new_unavailability='CitedMPR2004.05544:404 wholeworkallnewdelivery;distinctoriginal2005.13666 notsamework',ready=ready)))
