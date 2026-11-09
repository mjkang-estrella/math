"""Root documentary intake and disjoint routing, without mathematical execution."""
import os,resource
os.sched_setaffinity(0,sorted(os.sched_getaffinity(0))[:2])
resource.setrlimit(resource.RLIMIT_CPU,(120,120));resource.setrlimit(resource.RLIMIT_AS,(6*1024**3,6*1024**3))
from pathlib import Path
import json,hashlib,datetime,collections,re,base64,importlib.util
P=Path(__file__).resolve().parent.parent;ROOT=P/'root-intake-r60';A=P/'expanded-corpus-r464'
def sha(q):return hashlib.sha256(q.read_bytes()).hexdigest()
def dg(b):return hashlib.sha256(b).hexdigest()
def save(q,v):
 assert not q.exists(),str(q)
 q.write_text(json.dumps(v,indent=2)+'\n')
now=datetime.datetime.now(datetime.timezone.utc).isoformat()
assert json.loads((P/'ledger.json').read_text())['accepted_new']==57
routing=json.loads((ROOT/'selection-routing-r464.json').read_text())
assert sha(A/'TASK.txt')==routing['task_sha256'] and sha(A/'reservation.json')==routing['reservation_sha256']
manifest=json.loads((A/'MANIFEST.json').read_text());entries={x['path']:x for x in manifest['files']};assert len(entries)==181
for n,v in entries.items():
 assert not Path(n).is_absolute() and '..' not in Path(n).parts
 q=A/n;assert not q.is_symlink() and sha(q)==v['sha256'] and q.stat().st_size==v['bytes'],n
exclusions=manifest['terminal_noncircular_exclusions']
assert {str(q.relative_to(A)) for q in A.rglob('*') if q.is_file()}==set(entries)|set(exclusions)
frozen=json.loads((A/'frozen-inputs.json').read_text());assert len(frozen)==13 and all(Path(n).parent==A and sha(Path(n))==h for n,h in frozen.items())
after=json.loads((A/'frozen-after.json').read_text());assert after['count']==13 and after['mismatches']==[]
reservation=json.loads((A/'reservation.json').read_text());ids=reservation['ids'];gates=json.loads((A/'results.json').read_text());prov=json.loads((A/'literal-bindings.json').read_text())
assert len(ids)==20 and set(ids)==set(map(int,gates))=={x['id'] for x in prov}
chunks={}
for row in prov:
 key=str(row['id']);q=Path(row['chunk']);assert q.is_relative_to(P.parent/'lanes/pi-mathdb-full-corpus-inventory-r301/corpus')
 if str(q) not in chunks:
  b=q.read_bytes();chunks[str(q)]=(dg(b),b.splitlines(keepends=True))
 h,lines=chunks[str(q)];assert h==row['chunk_sha256'];raw=lines[row['line']-1]
 assert dg(raw)==row['raw_sha256'] and row['newline'] is True and raw.endswith(b'\n') and (A/f'originals/{key}.jsonl').read_bytes()==base64.b64decode(row['raw_base64'],validate=True)==raw
 obj=json.loads(raw);assert obj['mathdb_id']==row['id'] and obj==row['record']
 token=re.search(rb'"statement"\s*:\s*("(?:[^"\\]|\\.)*")',raw)[1]
 assert token.decode()==row['raw_statement_token'] and dg(token)==row['token_sha256'] and (A/f'originals/{key}.statement-token.json').read_bytes()==token
 assert json.loads(token)==obj['statement']==row['statement'] and dg(obj['statement'].encode())==row['statement_sha256']
 assert (A/f'originals/{key}.statement.txt').read_bytes()==obj['statement'].encode()
 assert gates[key]['literal']['statement']==obj['statement'] and gates[key]['acceptance']['credit']==0
receipts=[]
for q in sorted(A.glob('*.receipt.json')):
 v=json.loads(q.read_text());assert v['cwd']==str(A) and v['cpu_limit_s']==115 and v['as_limit_bytes']==6*1024**3 and v['deadline_s']==130
 receipts.append(dict(path=q.name,sha256=sha(q),exit=v['exit']))
assert json.loads((A/'terminal_manifest.receipt.json').read_text())['exit']==0
budget=json.loads((A/'search-budget.json').read_text());assert budget['calls_used']==3 and budget['queries_used']==9
charges=[json.loads(s) for s in (A/'search-charges.jsonl').read_text().splitlines()];assert len(charges)==3
previous=dict(calls_used=0,queries_used=0,maximum_calls=3,maximum_queries=9,charged_before_call=True)
for i,c in enumerate(charges,1):
 assert c['sequence']==i and c['before']==previous and sha(A/c['plan'])==c['plan_sha256']
 assert json.loads((A/c['plan']).read_text())['queries']==c['queries']
 expected=dict(previous);expected['calls_used']+=1;expected['queries_used']+=len(c['queries']);assert c['after']==expected;previous=expected
 response=json.loads((A/f"search-{['one','two','three'][i-1]}-response.json").read_text());assert response
assert previous==budget and sha(A/'charge_search.py')==sha(ROOT/'charge_search.py')
events=[json.loads(s) for s in (A/'guard-ledger.jsonl').read_text().splitlines()];counts=collections.Counter(e['event'] for e in events);assert counts==dict(attempt=6,success=6)
for e in events:
 if e['event']=='success':assert sha(A/e['destination'])==e['sha256'] and (A/e['destination']).stat().st_size==e['bytes']
record=dict(utc=now,source_lane=str(A),manifest_sha256=sha(A/'MANIFEST.json'),verified_manifest_files=181,verified_original_bindings=sorted(ids),verified_frozen_bindings=13,routing_pins='Actual task and reservation hashes match retained ROOT genesis',runner_receipts=receipts,receipt_exit_counts=dict(collections.Counter(str(x['exit']) for x in receipts)),guard_events=dict(counts),search_budget=budget,search_counter_continuity='Live old/new states, exact plan digests/querystrings, final counter and immutable helper authenticated; all three full saved response files parsed',root_disposition='ZERO_QUALIFIED_SURVIVORS_PUBLIC_AND_CORRECTION_EXCLUSIONS_RETAINED',scientific_summary='351661balancedVmulticolor Ramsey upperbound induction losesonedimension; coatomcolor/branchcompatibility andsharpflag lemma unpaid, source2color/m1propercases0.332619allnDeltaY/YDelta apexmove families propagation fails newapexvertex and commonface compatibilities; uniformminor/apexcertificate/core reduction unpaid, publicbases/immediatedescendants0.352903triangleTutte literalrefutation only printed exponentplacement error alreadycontradicted byactualprecedingProp1.11, sourcecorrection0.356183intendedmagicrectangle theoremactualYuFengLiu2410.23662with fullSylow2/exception conversionpublic0, samefamilyr460364348notrecount; missinggroupcardinalitycorrection0.343484actualHodges2311.07078Th1.1 fullpairedsandpile distributionpublic0 with perfectsymmetricdualityconvention,p2included.338009actualsource1712.07702v3 explicitlyfalseConj4.1viaTh3.6public0; notstrongerTutteconnectivity4.2/4.3. Fourreservedoriginalsread,twoadditionalcomparisons,sixteenreservedoriginalsunread/fourteenIDsnobodycomparison.',all20_gates=gates,new_denials=False,process='Preserved conclusion_proof_reads exit1 absenttextlabel and changedUnicodeawarerecovery, no knownaccesspolicy/counterviolation. Savedfullcapped largeoutputs and materialrecoveries retained. Tutteprimaryp161visuallyinspected; otherproofs/tablesattributedexactinventorydepth,notallbodyindependentproofaudits. Sampled/native/writer peak limits retained; no universal processcompliance claim.',root_scope='Documentary integrity/provenance/routing only; no root mathematical solving/programs/Lean/checkers',external_inputs='Preserved documentary inventories not recursively traversed or historical certificate audited; explicit frozen13 and immutable20raw-token-decoded bindings separately verified',credit=0,accepted_new=57,target_new=60,formal_dispatch=False,terminal_self_exclusions=exclusions)
save(P/'expanded-corpus-r464-parent-integration.json',record)
den=json.loads((ROOT/'inherited-denials-r465.json').read_text());den['utc']=now
den['root_r464_scope']='No newdenials.351661allkV Ramsey dimension/coatomgap;332619allnapexmove newapex/face/minorcertificate gap.352903sourceexponentplacementcorrection0,356183actualYuFengLiu2410.23662public0/samefamily364348notrecount,343484actualHodges2311.07078pairedsymmetricdistributionpublic0,338009sourceownfalse4.1notstronger4.2/4.3.181ownmanifest20rawtokenbindings13frozenverified,6GETsuccess3search9queries. No qualifiedsurvivor or credit.'
denpath=ROOT/'inherited-denials-r466.json';save(denpath,den)
base=json.loads((ROOT/'r465-config.json').read_text())
steering=base['steering']+'\nLATEST completed r464 adds zero qualified survivors and no denials. 351661 all-color balanced-V Ramsey upper bound still lacks the one lost dimension/coatom compatibility lemma; source two-color and all-mi1 cases do not settle arbitraryk. 332619 arbitrary-n apex move-family propagation still fails when the new Y-vertex is in an apex set and when minor witnesses lack a common face; bases/immediate descendants are source-known. 352903 exact triangle-polynomial refutation exposes only a public exponent-placement error already forced by preceding Proposition1.11, zero. 356183 intended magic-rectangle criterion is actual Yu-Feng-Liu2410.23662, same already-public family as364348; omitted cardinality is a correction, not extra credit. 343484 actual Hodges2311.07078Th1.1 supplies exact paired sandpile distribution, including p2, under source perfect symmetric-duality convention; arbitrary nonsymmetric-pairing extension changes scope. 338009 is source-own false Conjecture4.1 via actual1712.07702v3Th3.6, not the stronger Tutte-connectivity replacement4.2/4.3. Four originals read, sixteen originals unread; fourteen IDs no body comparison. Root verified181 ownfiles,20original bindings,13frozen inputs. No new independent mathematics, formal dispatch or credit.\n'
config=dict(number=466,protected_peers=['expanded-corpus-r463','expanded-corpus-r465'],completed_discovery_numbers=list(range(421,463))+[464],denials=str(denpath),excluded_ids=base['excluded_ids'],excluded_sources=base['excluded_sources'],peer_routing_files=['selection-routing-r463.json','selection-routing-r465.json'],steering=steering)
save(ROOT/'r466-config.json',config)
spec=importlib.util.spec_from_file_location('root_discovery_packet',ROOT/'prepare_discovery_packet.py');module=importlib.util.module_from_spec(spec);spec.loader.exec_module(module);ready=module.prepare(config)
print(json.dumps(dict(accepted_new=57,manifest_files=181,original_bindings=20,frozen_bindings=13,receipt_exit_counts=record['receipt_exit_counts'],new_denials=False,ready=ready)))
