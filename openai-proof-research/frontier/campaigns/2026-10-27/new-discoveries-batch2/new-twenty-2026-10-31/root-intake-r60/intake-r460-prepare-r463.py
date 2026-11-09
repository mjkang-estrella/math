"""Root-only documentary intake and disjoint assignment preparation."""
import os,resource
os.sched_setaffinity(0,sorted(os.sched_getaffinity(0))[:2])
resource.setrlimit(resource.RLIMIT_CPU,(120,120));resource.setrlimit(resource.RLIMIT_AS,(6*1024**3,6*1024**3))
from pathlib import Path
import json,hashlib,datetime,collections,re,importlib.util
from urllib.parse import urlsplit,unquote
P=Path(__file__).resolve().parent.parent;ROOT=P/'root-intake-r60';A=P/'expanded-corpus-r460'
def sha(q):return hashlib.sha256(q.read_bytes()).hexdigest()
def dg(b):return hashlib.sha256(b).hexdigest()
def save(q,v):
 assert not q.exists(),str(q)
 q.write_text(json.dumps(v,indent=2)+'\n')
now=datetime.datetime.now(datetime.timezone.utc).isoformat()
assert json.loads((P/'ledger.json').read_text())['accepted_new']==57
routing=json.loads((ROOT/'selection-routing-r460.json').read_text())
assert sha(A/'TASK.txt')==routing['task_sha256'] and sha(A/'reservation.json')==routing['reservation_sha256']
manifest=json.loads((A/'BYTE-MANIFEST.json').read_text());entries=manifest['files'];assert len(entries)==210
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
 assert dg(raw)==row['raw_line_sha256'] and row['newline'] and raw.endswith(b'\n') and (A/f'originals/{key}.jsonl').read_bytes()==raw
 obj=json.loads(raw);assert obj['mathdb_id']==int(key) and obj==row['record']
 token=re.search(rb'"statement"\s*:\s*("(?:[^"\\]|\\.)*")',raw)[1]
 assert dg(token)==row['token_sha256'] and (A/f'originals/{key}.statement-token.json').read_bytes()==token
 assert json.loads(token)==obj['statement'] and dg(obj['statement'].encode())==row['decoded_sha256']
 assert (A/f'originals/{key}.statement.txt').read_bytes()==obj['statement'].encode()
 assert gates[key]['literal']['decoded']==f'originals/{key}.statement.txt' and gates[key]['literal']['raw_token']==f'originals/{key}.statement-token.json' and gates[key]['literal']['original']==f'originals/{key}.jsonl'
 assert gates[key]['acceptance']['credit']==0
receipts=[]
for q in sorted(A.glob('*.receipt.json')):
 v=json.loads(q.read_text());assert v['cwd']==str(A) and v['cpu_limit_s']==115 and v['as_limit_bytes']==6*1024**3 and v['deadline_s']==130
 receipts.append(dict(path=q.name,sha256=sha(q),exit=v['exit']))
assert json.loads((A/'seal_manifest.receipt.json').read_text())['exit']==0
budget=json.loads((A/'search-budget.json').read_text());assert budget['calls_used']==3 and budget['queries_used']==9
charges=[json.loads(s) for s in (A/'search-charges.jsonl').read_text().splitlines()];assert len(charges)==3
previous=dict(calls_used=0,queries_used=0,maximum_calls=3,maximum_queries=9,charged_before_call=True)
for i,c in enumerate(charges,1):
 assert c['sequence']==i and c['before']==previous and sha(A/c['plan'])==c['plan_sha256']
 assert json.loads((A/c['plan']).read_text())['queries']==c['queries']
 expected=dict(previous);expected['calls_used']+=1;expected['queries_used']+=len(c['queries']);assert c['after']==expected;previous=expected
 response=json.loads((A/f'search-response-{i}.json').read_text());assert response
assert previous==budget and sha(A/'charge_search.py')==sha(ROOT/'charge_search.py')
events=[json.loads(s) for s in (A/'guard-ledger.jsonl').read_text().splitlines()];counts=collections.Counter(e['event'] for e in events);assert counts==dict(attempt=12,success=11,unavailable=1)
for e in events:
 if e['event']=='success':assert sha(A/e['destination'])==e['sha256'] and (A/e['destination']).stat().st_size==e['bytes']
failure=next(e for e in events if e['event']=='unavailable');assert failure['status'] is None and 'gaierror' in failure['error'] and failure['url']=='https://n.ethz.ch/~ywigderson/math/publications/Hedetniemi.pdf'
plan=json.loads((A/'get-he-wigderson.json').read_text());assert plan['url']==failure['url'] and plan['routes']==['344593']
record=dict(utc=now,source_lane=str(A),manifest_sha256=sha(A/'BYTE-MANIFEST.json'),verified_manifest_files=210,verified_original_bindings=sorted(ids),verified_frozen_bindings=13,routing_pins='Actual task and reservation hashes match retained ROOT genesis',runner_receipts=receipts,receipt_exit_counts=dict(collections.Counter(str(x['exit']) for x in receipts)),guard_events=dict(counts),search_budget=budget,search_counter_continuity='Live old/new states, exact plan digests/querystrings, final counter and immutable helper authenticated; all three full saved response files parsed',root_disposition='ZERO_QUALIFIED_SURVIVORS_PUBLIC_AND_COMPLETE_ADAPTATION_EXCLUSIONS_RETAINED',scientific_summary='344593author ordinary trianglefree Hedetniemi refutation via actualShitov productcounterexample and actualKun sparse relational replacement: orientation avoids symmetricrelation2cycle issue, full finitechromaticobstruction and twohomomorphism productcoloring bridge; additional symbolic probabilistic specialtransfer proof, complete routineadaptation0 with contrarycase preserved, no claim exactcorollary previouslyprinted.364348actualYuFengLiu2410.23662v1 publicfullmagicrectangle characterization with Sylow2/involution and dimensionexception bridges0.339729sumvsdifference and352334rainbowhypothesis corrections0.340541assignedferromagneticcliqueconverse distinctfromknownfalse antiferromagneticbicliqueconverse, no neighbor transfer.339365arbitrarycyclicoverlap legalincrease and340146sourcepositiveselfdistance/SNCgeneraldegree gaps unpaid. Thirteen reserved original bodies unread.',all20_gates=gates,new_denial=dict(work='He-Wigderson Hedetniemi conjecture asymptotically false author primary manuscript, exact author Hedetniemi.pdf route',event=failure,plan=plan,scope='ENTIREidentifiedwork ALLnewalternate hosts/versions/arxiv/author/cache/mirror/DOI/API/body/metadata deliveries unavailable. Distinct Shitov1905.02167 and Kun0706.1701 papers acquired separately are not alternate delivery of this failedwork; adaptation bridge doesnot depend on failed HeWigderson work. No retry or indirect recovery.'),process='Preserved get_he_wigderson exit1 DNSresolutionfailure, not a demonstrated guardpolicy/counter violation; no retry/alternate delivery reported. Large saved instruction/history/source displays recovered at relevant bounded passages. No visual figure/matrix inspection claimed, actual YuFengLiu tableproof reading extractedtext only. Sampled/native/writer peak limits retained; no universal processcompliance claim.',root_scope='Documentary integrity/provenance/routing only; no root mathematical solving/programs/Lean/checkers',external_inputs='Preserved documentary inventories not recursively traversed or historical certificate audited; explicit frozen13 and immutable20raw-token-decoded bindings separately verified',credit=0,accepted_new=57,target_new=60,formal_dispatch=False,terminal_self_exclusions=exclusions)
record['root_reader_deviation']='First root verifier assumed literal.decoded contained text; actual schema contains an exact own-lane statement-file path. Assertion failed before any mutation. Changed verifier pins all three exact evidence paths and independently verifies their actual bytes against corpus raw/token/decoded values. Worker artifacts unchanged; no failed check relabeled as pass.'
save(P/'expanded-corpus-r460-parent-integration.json',record)
den=json.loads((ROOT/'inherited-denials-r462.json').read_text());den['utc']=now
den['blocked_keys']=sorted(set(den['blocked_keys'])|{urlsplit(failure['url']).hostname.lower()+unquote(urlsplit(failure['url']).path).rstrip('/')})
den['blocked_artifacts']=sorted(set(den['blocked_artifacts'])|{'he-wigderson hedetniemi conjecture asymptotically false','n.ethz.ch/~ywigderson/math/publications/hedetniemi.pdf'})
den['records'].append(dict(url=failure['url'],reason=dict(status='DNSgaierror(-5)',artifact='He-Wigderson Hedetniemi conjecture asymptotically false author primary manuscript',restriction='Entireidentifiedwork ALLnewalternate host/query/version/arxiv/author/cache/mirror/DOI/API/body/metadata deliveries unavailable. Actualbody unread, no retry or alternate lookup/delivery. Different Shitov1905.02167 and Kun0706.1701 papers separately acquired are not samefailedwork, nor is original1911.09799.'),evidence=dict(path=str(A/'guard-ledger.jsonl'),sha256=sha(A/'guard-ledger.jsonl'),plan=str(A/'get-he-wigderson.json'),plan_sha256=sha(A/'get-he-wigderson.json'))))
den['root_r460_scope']='344593completeauthorordinary trianglefree refutation and fullShitovKun sparsehomomorphic transfer routineadaptation0;364348exactYuFengLiu2410.23662fullpublictheorem0;339729/352334sourcecorrections0;340541ferromagneticcliquenotfalseantiferromagneticbicliqueconverse.339365overlapincrease and340146sourceSNCgaps. HeWigdersonauthorHedetniemi.pdf DNSfailurewholeworkallnewdeliveryunavailable, notdifferentShitov/Kun/original1911.09799.210ownmanifest20rawtokenbindings13frozenverified,12GEThops11payloads1DNSfailure,3search9queries. No qualifiedsurvivor or credit.'
denpath=ROOT/'inherited-denials-r463.json';save(denpath,den)
base=json.loads((ROOT/'r462-config.json').read_text())
steering=base['steering']+'\nLATEST completed r460 has zero qualified survivors. 344593 author ordinary triangle-free product-chromatic counterexample comes from a COMPLETE actual Shitov1905.02167 plus Kun0706.1701 sparse-homomorphic replacement bridge, including relational orientation/girth encoding and product coloring; routine adaptation zero, strongest contrary significance case preserved, no claim earlier exact corollary was printed. A separate symbolic probabilistic proof pays the needed sparse special case but does not create another credited family. 364348 is the actual Yu-Feng-Liu2410.23662v1 full public magic-rectangle characterization, with exact Sylow2/involution and exceptional-dimension conversion, zero. 339729 sum/difference and352334rainbowhypothesis errors are source corrections zero. Assigned340541ferromagnetic/clique converse is DISTINCT from the known false antiferromagnetic/biclique converse; do not transfer its counterexample. 339365arbitrary cyclic-overlap legal-increase and340146positive-self-distance/SNC general-degree gaps remain unpaid. Thirteen original bodies unread. He-Wigderson Hedetniemi conjecture asymptotically false author primary manuscript at n.ethz.ch/~ywigderson/math/publications/Hedetniemi.pdf failed DNS resolution. ENTIRE identified work is unavailable for ALL new alternate hosts/versions/arxiv/authors/caches/mirrors/DOI/API/body/metadata deliveries; no retry or indirect recovery. Distinct Shitov, Kun, and original1911.09799 are not that failed work. Root verified210 ownfiles,20original bindings,13frozen inputs; no independent mathematical PASS or new credit.\n'
config=dict(number=463,protected_peers=['expanded-corpus-r461','expanded-corpus-r462'],completed_discovery_numbers=list(range(421,461)),denials=str(denpath),excluded_ids=base['excluded_ids'],excluded_sources=base['excluded_sources'],peer_routing_files=['selection-routing-r461.json','selection-routing-r462.json'],steering=steering)
save(ROOT/'r463-config.json',config)
spec=importlib.util.spec_from_file_location('root_discovery_packet',ROOT/'prepare_discovery_packet.py');module=importlib.util.module_from_spec(spec);spec.loader.exec_module(module);ready=module.prepare(config)
print(json.dumps(dict(accepted_new=57,manifest_files=210,original_bindings=20,frozen_bindings=13,receipt_exit_counts=record['receipt_exit_counts'],new_unavailability='HeWigderson author Hedetniemi.pdf:DNS wholeworkallnewdelivery;distinctShitov/Kun/original1911.09799 notsamework',ready=ready)))
