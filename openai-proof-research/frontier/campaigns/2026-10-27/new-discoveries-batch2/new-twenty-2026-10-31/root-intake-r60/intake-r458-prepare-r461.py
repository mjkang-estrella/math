"""Root-only integrity/routing intake; no mathematics, network or formal execution."""
import os,resource
os.sched_setaffinity(0,sorted(os.sched_getaffinity(0))[:2])
resource.setrlimit(resource.RLIMIT_CPU,(120,120));resource.setrlimit(resource.RLIMIT_AS,(6*1024**3,6*1024**3))
from pathlib import Path
import json,hashlib,datetime,collections,re,importlib.util
from urllib.parse import urlsplit,unquote
P=Path(__file__).resolve().parent.parent;ROOT=P/'root-intake-r60';A=P/'expanded-corpus-r458'
def sha(q):return hashlib.sha256(q.read_bytes()).hexdigest()
def dg(b):return hashlib.sha256(b).hexdigest()
def save(q,v):
 assert not q.exists(),str(q)
 q.write_text(json.dumps(v,indent=2)+'\n')
now=datetime.datetime.now(datetime.timezone.utc).isoformat()
assert json.loads((P/'ledger.json').read_text())['accepted_new']==57
routing=json.loads((ROOT/'selection-routing-r458.json').read_text())
assert sha(A/'TASK.txt')==routing['task_sha256'] and sha(A/'reservation.json')==routing['reservation_sha256']
manifest=json.loads((A/'SHA256-MANIFEST.json').read_text());entries={x['path']:x for x in manifest['files']};assert len(entries)==156
for n,v in entries.items():
 assert not Path(n).is_absolute() and '..' not in Path(n).parts
 q=A/n;assert not q.is_symlink() and sha(q)==v['sha256'] and q.stat().st_size==v['bytes'],n
exclusions=manifest['terminal_non_circular_exclusions']
assert {str(q.relative_to(A)) for q in A.rglob('*') if q.is_file()}==set(entries)|set(exclusions)
frozen=json.loads((A/'frozen-inputs.json').read_text());assert len(frozen)==13 and all(Path(n).parent==A and sha(Path(n))==h for n,h in frozen.items())
after=json.loads((A/'frozen-after.json').read_text());assert after['count']==13 and after['mismatches']==[]
reservation=json.loads((A/'reservation.json').read_text());ids=reservation['ids'];gates=json.loads((A/'EXACT20.json').read_text())
prov=json.loads((A/'original-bindings.json').read_text());assert len(ids)==20 and set(ids)==set(map(int,gates))=={x['id'] for x in prov}
chunks={}
for row in prov:
 key=str(row['id']);q=Path(row['chunk']);assert q.is_relative_to(P.parent/'lanes/pi-mathdb-full-corpus-inventory-r301/corpus')
 if str(q) not in chunks:
  b=q.read_bytes();chunks[str(q)]=(dg(b),b.splitlines(keepends=True))
 h,lines=chunks[str(q)];assert h==row['chunk_sha256'];raw=lines[row['line']-1]
 assert dg(raw)==row['raw_sha256'] and row['newline'] and raw.endswith(b'\n') and (A/f'originals/{key}.jsonl').read_bytes()==raw
 obj=json.loads(raw);assert obj['mathdb_id']==row['id'] and obj==row['record']
 token=re.search(rb'"statement"\s*:\s*("(?:[^"\\]|\\.)*")',raw)[1]
 assert token.decode()==row['raw_statement_token'] and dg(token)==row['raw_statement_token_sha256']
 assert json.loads(token)==row['decoded_statement']==obj['statement'] and dg(obj['statement'].encode())==row['decoded_utf8_sha256']
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
 response=json.loads((A/f"search-response-{['one','two'][i-1]}.json").read_text());assert response
assert previous==budget and sha(A/'charge_search.py')==sha(ROOT/'charge_search.py')
events=[json.loads(s) for s in (A/'guard-ledger.jsonl').read_text().splitlines()];counts=collections.Counter(e['event'] for e in events)
assert counts==dict(attempt=6,success=5,unavailable=1)
for e in events:
 if e['event']=='success':assert sha(A/e['destination'])==e['sha256'] and (A/e['destination']).stat().st_size==e['bytes']
failure=next(e for e in events if e['event']=='unavailable');assert failure['status']==403 and 'qt1qg5647z' in failure['url']
plan=json.loads((A/'get-chords-final.json').read_text());assert plan['url']==failure['url'] and plan['routes']==['350310']
record=dict(utc=now,source_lane=str(A),manifest_sha256=sha(A/'SHA256-MANIFEST.json'),verified_manifest_files=156,verified_original_bindings=sorted(ids),verified_frozen_bindings=13,routing_pins='Actual task and reservation hashes match retained ROOT genesis',runner_receipts=receipts,receipt_exit_counts=dict(collections.Counter(str(x['exit']) for x in receipts)),guard_events=dict(counts),search_budget=budget,search_counter_continuity='Live old/new states, exact plan digests/querystrings, final counter and immutable helper authenticated; both full saved responses parsed',root_disposition='ZERO_QUALIFIED_SURVIVORS',scientific_summary='355751source-own exact tangled/quasi-tangled counts plus explicit nonnegative-product subtraction supplies full intendedn>=2 routine bridge, zero; singleton sorting-time issue endpoint correction zero.356893actualEMSfinal recovers corruptfield/parameterstatement, source-own splitsemisimple/n2caseszero, fullalln triangular multiplication/parameter/field/characteristic bridge unpaid.350310inside-outside matching/cubicity/twoedgecut route lacks exact reverse connectivity/rootorientation multiplicity; specific finalsource-own construction actualbody403unavailable, searchsnippetnotproof. Seventeen original source bodies unread. No independent validation or qualified full result.',all20_gates=gates,new_denial=dict(work='Nabergall The combinatorics of a tree-like functional equation for connected chord diagrams; Combinatorial Theory3(3)(2023)#8; original2104.02296',event=failure,plan=plan,scope='ENTIREidentifiedwork ALLnewalternate host/query/version/arxiv/author/cache/mirror/DOI/API/body/metadata deliveries unavailable; explicitly saved predenialv1only, not finalequivalence; no retry or indirect recovery'),process='Preserved get_chords_final exit1 HTTP403, no alternate delivery or guard/budget rejection reported. Truncated literal/denial/history outputs recovered before scientific prioritization. Material visual limit p17promotion not successfully displayed, chordsfigures not audited, BenkartElduque20-21textcaptiononly; actual inventories retain exact depth. Sampled/native/writer peak limits retained; no universal compliance claim.',root_scope='Documentary integrity/provenance/routing only; no root mathematical solving/programs/Lean/checkers',external_inputs='Preserved documentary inventories not recursively traversed or historical certificate audited; explicit frozen13 and immutable20raw-token-decoded bindings separately verified',credit=0,accepted_new=57,target_new=60,formal_dispatch=False,terminal_self_exclusions=exclusions)
save(P/'expanded-corpus-r458-parent-integration.json',record)
den=json.loads((ROOT/'inherited-denials-r459.json').read_text());den['utc']=now
den['blocked_keys']=sorted(set(den['blocked_keys'])|{urlsplit(failure['url']).hostname.lower()+unquote(urlsplit(failure['url']).path).rstrip('/')})
den['blocked_artifacts']=sorted(set(den['blocked_artifacts'])|{'2104.02296','qt1qg5647z','the combinatorics of a tree-like functional equation for connected chord diagrams'})
den['records'].append(dict(url=failure['url'],reason=dict(status=403,artifact='Nabergall The combinatorics of a tree-like functional equation for connected chord diagrams, CombinatorialTheory3(3)(2023)#8, source2104.02296',restriction='Entireidentifiedwork ALLnewalternate host/query/version/arxiv/author/cache/mirror/DOI/API/body/metadata deliveries unavailable. Explicitlycopied predenialoriginalv1only, notfinalequivalence. Actual finalFig8.3construction only searchnavigation, not proof. No retry or indirect recovery.'),evidence=dict(path=str(A/'guard-ledger.jsonl'),sha256=sha(A/'guard-ledger.jsonl'),plan=str(A/'get-chords-final.json'),plan_sha256=sha(A/'get-chords-final.json'))))
den['root_r458_scope']='355751complete source-count-to-intendedinequality routinebridge0, singletoncorrection0.356893actualEMSfieldparameterrepair0/sourceownpropercases0, fullalgebramapfieldchar gaps.350310cubicchordmap exactroot/multiplicity/reverseconnectivity gaps, finalNabergall2023CombinatorialTheory3(3)#8/source2104.02296/escholarshipqt1qg5647z403 ALLnewdeliveryunavailable.156ownmanifest20rawtokenbindings13frozenverified,6GETattempts5payloads1HTTP403,2search6queries. No qualifiedsurvivor or credit.'
denpath=ROOT/'inherited-denials-r461.json';save(denpath,den)
base=json.loads((ROOT/'r460-config.json').read_text())
steering=base['steering']+'\nLATEST completed r458 adds zero qualified survivors. 355751 intended n>=2 tangled/quasi-tangled inequality follows by a COMPLETE nonnegative-product subtraction from the source own exact counts; literal singleton correction is also zero. 356893 actual EMS final recovers missing field/parameter hypotheses; the full all-n arbitrary-field map, multiplication, bad parameters and characteristic cases remain unpaid, while source-own split-semisimple/n=2 cases are zero. 350310 planar inside/outside chord construction does not yet pay reverse connectivity and exact map rooting/orientation multiplicities. The specifically identified final Nabergall paper The combinatorics of a tree-like functional equation for connected chord diagrams, Combinatorial Theory 3(3)(2023) paper8, original 2104.02296, escholarship qt1qg5647z, returned HTTP403. ENTIRE work is unavailable for ALL new host/query/version/arXiv/author/cache/mirror/DOI/API/body/metadata deliveries. No retries or indirect recovery; explicitly copied pre-denial v1 is not final equivalence. Search excerpt identifying Fig8.3 construction is navigation, not an authenticated proof. Seventeen original bodies were unread. Root verified all156 own manifested files, twenty raw/token/decoded bindings and thirteen frozen inputs. No independent mathematical PASS, formal dispatch or credit.\n'
config=dict(number=461,protected_peers=['expanded-corpus-r459','expanded-corpus-r460'],completed_discovery_numbers=list(range(421,459)),denials=str(denpath),excluded_ids=base['excluded_ids'],excluded_sources=base['excluded_sources'],peer_routing_files=['selection-routing-r459.json','selection-routing-r460.json'],steering=steering)
save(ROOT/'r461-config.json',config)
spec=importlib.util.spec_from_file_location('root_discovery_packet',ROOT/'prepare_discovery_packet.py');module=importlib.util.module_from_spec(spec);spec.loader.exec_module(module);ready=module.prepare(config)
print(json.dumps(dict(accepted_new=57,manifest_files=156,original_bindings=20,frozen_bindings=13,receipt_exit_counts=record['receipt_exit_counts'],new_unavailability='Nabergall2023CombinatorialTheory3(3)#8/source2104.02296/qt1qg5647z:403 wholeworkallnewdelivery',ready=ready)))
