"""Root documentary intake only; mathematical findings remain attributed."""
import os,resource
os.sched_setaffinity(0,sorted(os.sched_getaffinity(0))[:2])
resource.setrlimit(resource.RLIMIT_CPU,(120,120));resource.setrlimit(resource.RLIMIT_AS,(6*1024**3,6*1024**3))
from pathlib import Path
import json,hashlib,datetime,collections,re,importlib.util
P=Path(__file__).resolve().parent.parent;ROOT=P/'root-intake-r60';A=P/'expanded-corpus-r461'
def sha(q):return hashlib.sha256(q.read_bytes()).hexdigest()
def dg(b):return hashlib.sha256(b).hexdigest()
def save(q,v):
 assert not q.exists(),str(q)
 q.write_text(json.dumps(v,indent=2)+'\n')
now=datetime.datetime.now(datetime.timezone.utc).isoformat()
assert json.loads((P/'ledger.json').read_text())['accepted_new']==57
routing=json.loads((ROOT/'selection-routing-r461.json').read_text())
assert sha(A/'TASK.txt')==routing['task_sha256'] and sha(A/'reservation.json')==routing['reservation_sha256']
manifest=json.loads((A/'MANIFEST.json').read_text());entries={x['path']:x for x in manifest['files']};assert len(entries)==202
for n,v in entries.items():
 assert not Path(n).is_absolute() and '..' not in Path(n).parts
 q=A/n;assert not q.is_symlink() and sha(q)==v['sha256'] and q.stat().st_size==v['bytes'],n
exclusions=manifest['terminal_non_circular_exclusions']
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
 assert dg(raw)==row['raw_sha256'] and row['newline']=='LF' and raw.endswith(b'\n') and (A/f'literals/{key}.raw.jsonl').read_bytes()==raw
 obj=json.loads(raw);assert obj['mathdb_id']==row['id'] and obj==row['object']
 token=re.search(rb'"statement"\s*:\s*("(?:[^"\\]|\\.)*")',raw)[1]
 assert dg(token)==row['token_sha256'] and (A/f'literals/{key}.token.json').read_bytes()==token
 assert json.loads(token)==obj['statement'] and dg(obj['statement'].encode())==row['decoded_sha256']
 assert (A/f'literals/{key}.statement.txt').read_bytes()==obj['statement'].encode()
 assert gates[key]['literal_statement']==obj['statement'] and gates[key]['acceptance']['credit']==0
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
 response=json.loads((A/f"search-{['one','two'][i-1]}-response.json").read_text());assert response
assert previous==budget and sha(A/'charge_search.py')==sha(ROOT/'charge_search.py')
events=[json.loads(s) for s in (A/'guard-ledger.jsonl').read_text().splitlines()];counts=collections.Counter(e['event'] for e in events);assert counts==dict(attempt=7,success=7)
for e in events:
 if e['event']=='success':assert sha(A/e['destination'])==e['sha256'] and (A/e['destination']).stat().st_size==e['bytes']
record=dict(utc=now,source_lane=str(A),manifest_sha256=sha(A/'MANIFEST.json'),verified_manifest_files=202,verified_original_bindings=sorted(ids),verified_frozen_bindings=13,routing_pins='Actual task and reservation hashes match retained ROOT genesis',runner_receipts=receipts,receipt_exit_counts=dict(collections.Counter(str(x['exit']) for x in receipts)),guard_events=dict(counts),search_budget=budget,search_counter_continuity='Live old/new states, exact plan digests/querystrings, final counter and immutable helper authenticated; both full saved responses parsed',root_disposition='ZERO_QUALIFIED_SURVIVORS_PUBLIC_EXCLUSIONS_RETAINED',scientific_summary='333017actualFaberHarris2607.06171v1 fullprimary charging/layers generalizedstrictlyincreasingobjective theorem coversliteral, complete source-to-target bridge0.337512actualZhangChenChen2605.02793v1Th1.9Cor3.2 Gallai formula/proof coversliteral0; differentclassicalRamseyrefutation nottransferred.340514actualKelmansmath0607512R3 connectedcubic60vertexdomination21counterexample0, localgadgetrobustness lemma attributednotindependentlyreproved.336806k0literalpolarity/sourcewording inconsistency correction0.337425allgaussoidquadrics circuit/separatingvector lemma unpaid, spanninglistcompatibility not arbitrarylinearcombinationcompatibility.330519productincidencepalette alignment unpaid; regularsupergraphdegreepremise notliteralconsequence. Fouroriginals read,sixIDssomeactualprimarycomparison, fourteenoriginalsnotcleared; original1710.10455/1809.08987unreaddespite distinct relevantpublicpapers read.',all20_gates=gates,new_denials=False,process='Preserved read_cherries_proof exit1 missingheading and changedSection3recovery, notknownaccesspolicy/counterbreach. Earlier four-source-scope count corrected to actualfiveURLs in savedhitobjects; noexactreservedIDmatch/no neighbor transfer. Fullsavedlargeoutputs and materialrecoveries retained; twoincidencefigures visuallyinspected. Sampled/native/writer peak limitations retained; no universal processcompliance claim.',root_scope='Documentary integrity/provenance/routing only; no root mathematical solving/programs/Lean/checkers',external_inputs='Preserved documentary inventories not recursively traversed or historical certificate audited; explicit frozen13 and immutable20raw-token-decoded bindings separately verified',credit=0,accepted_new=57,target_new=60,formal_dispatch=False,terminal_self_exclusions=exclusions)
record['root_reader_deviation']='First root verifier expected an escaped newline marker, whereas this packet uses the literal metadata tagLF. Assertion failed before mutation; changed verifier pinsLF and independently checks every corpus raw byte sequence ends in byteLF and equals its preserved original. No worker changes or failed-check relabeling.'
save(P/'expanded-corpus-r461-parent-integration.json',record)
den=json.loads((ROOT/'inherited-denials-r463.json').read_text());den['utc']=now
den['root_r461_scope']='No newdenials.333017actualFaberHarris2607.06171generalizedobjectivefullpublictheorem0;337512actualZhangChenChen2605.02793Gallai theorem0 notclassicalRamseyrefutation;340514actualKelmansmath0607512connectedcubicR3publiccounterexample0 withlocallemmaattributed.336806polaritycorrection0.337425allquadriclinearcombination/separatingvector and330519globalincidencealignment gaps.202ownmanifest20rawtokenbindings13frozenverified,7GETsuccesses2search6queries. No qualifiedsurvivor or credit.'
denpath=ROOT/'inherited-denials-r464.json';save(denpath,den)
base=json.loads((ROOT/'r463-config.json').read_text())
additional='\nLATEST completed r461 adds zero qualified survivors and no denials. 333017 is actual Faber-Harris2607.06171v1 full public isolation theorem, including generalized strictly increasing objectives, with full charging/layer-to-literal bridge. 337512 is actual Zhang-Chen-Chen2605.02793v1 Gallai formula/proof, not its different classical Ramsey refutation. Both earn zero. 340514 actual Kelmans math/0607512 gives connected cubic R3 with60vertices and domination21>20; local gadget robustness lemma is attributed, not independently re-proved, no new witness certificate. 336806 obstruction-polarity/source typo yields only a correction, zero. 337425 compatibility with a spanning family does not imply compatibility with all linear combinations; all-n circuit or separating-vector lemma remains unpaid. 330519 global product-incidence palette alignment is unpaid; source regular-supergraph degree condition is not implied by literal assumptions, and irregular incidence coloring is not automatically square coloring. Four original sources read, six IDs some actual primary comparison, fourteen originals uncleared; original1710.10455 and1809.08987 remain unread despite distinct public follow-ups being read. Root verified202 ownfiles,20original bindings,13frozen inputs. No new independent mathematical PASS, formal dispatch or credit.\n'
config=dict(number=464,protected_peers=['expanded-corpus-r462','expanded-corpus-r463'],completed_discovery_numbers=list(range(421,462)),denials=str(denpath),excluded_ids=base['excluded_ids'],excluded_sources=base['excluded_sources'],peer_routing_files=['selection-routing-r462.json','selection-routing-r463.json'],steering=base['steering']+additional)
save(ROOT/'r464-config.json',config)
spec=importlib.util.spec_from_file_location('root_discovery_packet',ROOT/'prepare_discovery_packet.py');module=importlib.util.module_from_spec(spec);spec.loader.exec_module(module);ready=module.prepare(config)
# r463 has not been launched. Its immutable files remain byte-identical;
# this root-only dispatch addendum adds the newly planned peer and completed findings.
L=P/'expanded-corpus-r463';r463=json.loads((ROOT/'r463-ready.json').read_text())
assert not (L/'bootstrap-receipt.json').exists() and sha(L/'TASK.txt')==r463['task_sha256']
assert all(sha(Path(n))==h for n,h in json.loads((L/'frozen-inputs.json').read_text()).items())
save(ROOT/'r463-prelaunch-addendum.json',dict(utc=now,task_sha256=r463['task_sha256'],frozen_bindings=13,immutable_files_unchanged=True,additional_protected_planned_peer='expanded-corpus-r464',active_peers=['expanded-corpus-r462','expanded-corpus-r464'],completed_findings=additional,new_denials=False,scope='Root dispatch steering only; no child/frozen mutation or activepeer access'))
print(json.dumps(dict(accepted_new=57,manifest_files=202,original_bindings=20,frozen_bindings=13,receipt_exit_counts=record['receipt_exit_counts'],r463_immutable_unchanged=True,ready=ready)))
