"""Root integrity and metadata routing; no mathematical or formal execution."""
import os,resource
os.sched_setaffinity(0,sorted(os.sched_getaffinity(0))[:2])
resource.setrlimit(resource.RLIMIT_CPU,(120,120));resource.setrlimit(resource.RLIMIT_AS,(6*1024**3,6*1024**3))
from pathlib import Path
import json,hashlib,datetime,collections,re,importlib.util
P=Path(__file__).resolve().parent.parent;ROOT=P/'root-intake-r60';A=P/'expanded-corpus-r462'
def sha(q):return hashlib.sha256(q.read_bytes()).hexdigest()
def dg(b):return hashlib.sha256(b).hexdigest()
def save(q,v):
 assert not q.exists(),str(q)
 q.write_text(json.dumps(v,indent=2)+'\n')
now=datetime.datetime.now(datetime.timezone.utc).isoformat()
assert json.loads((P/'ledger.json').read_text())['accepted_new']==57
routing=json.loads((ROOT/'selection-routing-r462.json').read_text())
assert sha(A/'TASK.txt')==routing['task_sha256'] and sha(A/'reservation.json')==routing['reservation_sha256']
manifest=json.loads((A/'MANIFEST.json').read_text());entries={x['path']:x for x in manifest['files']};assert len(entries)==178
for n,v in entries.items():
 assert not Path(n).is_absolute() and '..' not in Path(n).parts
 q=A/n;assert not q.is_symlink() and sha(q)==v['sha256'] and q.stat().st_size==v['bytes'],n
exclusions=manifest['terminal_non_circular_exclusions']
assert {str(q.relative_to(A)) for q in A.rglob('*') if q.is_file()}==set(entries)|set(exclusions)
frozen=json.loads((A/'frozen-inputs.json').read_text());assert len(frozen)==13 and all(Path(n).parent==A and sha(Path(n))==h for n,h in frozen.items())
after=json.loads((A/'frozen-after.json').read_text());assert after['count']==13 and after['mismatches']==[]
reservation=json.loads((A/'reservation.json').read_text());ids=reservation['ids'];gates=json.loads((A/'results.json').read_text());prov=json.loads((A/'provenance.json').read_text());literals=json.loads((A/'literals.json').read_text())
assert len(ids)==20 and set(ids)==set(map(int,gates))=={x['id'] for x in prov}==set(map(int,literals))
chunks={}
for row in prov:
 key=str(row['id']);q=Path(row['chunk']);assert q.is_relative_to(P.parent/'lanes/pi-mathdb-full-corpus-inventory-r301/corpus')
 if str(q) not in chunks:
  b=q.read_bytes();chunks[str(q)]=(dg(b),b.splitlines(keepends=True))
 h,lines=chunks[str(q)];assert h==row['chunk_sha256'];raw=lines[row['line']-1]
 assert dg(raw)==row['raw_line_sha256'] and row['newline'] is True and raw.endswith(b'\n') and (A/f'originals/{key}.jsonl').read_bytes()==raw
 obj=json.loads(raw);assert obj['mathdb_id']==row['id'] and obj==literals[key]
 token=re.search(rb'"statement"\s*:\s*("(?:[^"\\]|\\.)*")',raw)[1]
 assert dg(token)==row['statement_token_sha256'] and (A/f'originals/{key}.statement-token.txt').read_bytes()==token
 assert json.loads(token)==obj['statement'] and dg(obj['statement'].encode())==row['statement_utf8_sha256']
 assert (A/f'originals/{key}.statement.txt').read_bytes()==obj['statement'].encode()
 assert gates[key]['literal']['raw']==f'originals/{key}.jsonl' and gates[key]['literal']['token']==f'originals/{key}.statement-token.txt' and gates[key]['literal']['decoded']==f'originals/{key}.statement.txt'
 assert gates[key]['acceptance']['credit']==0 and not gates[key]['qualified_survivor']
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
 response=json.loads((A/f'search-response{i}.json').read_text());assert response
assert previous==budget and sha(A/'charge_search.py')==sha(ROOT/'charge_search.py')
events=[json.loads(s) for s in (A/'guard-ledger.jsonl').read_text().splitlines()];counts=collections.Counter(e['event'] for e in events);assert counts==dict(attempt=4,success=4)
for e in events:
 if e['event']=='success':assert sha(A/e['destination'])==e['sha256'] and (A/e['destination']).stat().st_size==e['bytes']
record=dict(utc=now,source_lane=str(A),manifest_sha256=sha(A/'MANIFEST.json'),verified_manifest_files=178,verified_original_bindings=sorted(ids),verified_frozen_bindings=13,routing_pins='Actual task and reservation hashes match retained ROOT genesis',runner_receipts=receipts,receipt_exit_counts=dict(collections.Counter(str(x['exit']) for x in receipts)),guard_events=dict(counts),search_budget=budget,search_counter_continuity='Live old/new states, exact plan digests/querystrings, final counter and immutable helper authenticated; all three full saved response files parsed',root_disposition='ZERO_QUALIFIED_SURVIVORS_PUBLIC_REFUTATION_EXCLUSION_RETAINED',scientific_summary='331192exact coupled entangled-thread recursion doesnot factor competing maximuminitial even-thread connectors into Motzkin products; publiclayeredcases0.325688actualfinal two-variable Tutte contraction-ideal target not settled byx1specialization, generalactivityfiber/star-deletion elimination unpaid; original1306.0294unread/notfinalequivalence.326360branchstar quotient introduces incompatible generatorconjugations, arbitrarygroup specifiedprojected Cayleyminor bridge unpaid; source failure fordifferent semigroup notassignedrightzero conjecture.331491actualBekeCsajiCsikvariPituk2024final fullpublic matroid counterexample plus printed MdirectsumMdual bridge refutes allthreeinequalities, zero; graphicneighbor target notrefuted. Sixteen reserved original bodies unread;325688final and331491laterpublicrefutation readinstead. Specific directedCSP/snake publicsolutionproofclaims unreadHOLDs not snippetclearance.',all20_gates=gates,new_denials=False,process='No reported new accessfailure or cap/frozen/budget/protectedfile breach. Savedfull capped displays and bounded material recoveries retained. Actualsource-read inventory distinguishes definition/theorem/proof/figure depth; acquiredbody not full audit. Sampled/native/writer peak limits retained; no universal processcompliance claim.',root_scope='Documentary integrity/provenance/routing only; no root mathematical solving/programs/Lean/checkers',external_inputs='Preserved documentary inventories not recursively traversed or historical certificate audited; explicit frozen13 and immutable20raw-token-decoded bindings separately verified',credit=0,accepted_new=57,target_new=60,formal_dispatch=False,terminal_self_exclusions=exclusions)
save(P/'expanded-corpus-r462-parent-integration.json',record)
den=json.loads((ROOT/'inherited-denials-r464.json').read_text());den['utc']=now
den['root_r462_scope']='No newdenials.331192competingconnector Motzkinfiber factorization gap;325688x1specialization notQxyideal membership;326360specifiedCayleyminor conjugationcompatibility gap.331491actualBekeCsajiCsikvariPituk2024final and printed directsumdual bridge refutes allthree generalmatroid inequalities0, notgraphicneighborconjecture.178ownmanifest20rawtokenbindings13frozenverified,4GETsuccess3search9queries. No qualifiedsurvivor or credit.'
denpath=ROOT/'inherited-denials-r465.json';save(denpath,den)
base=json.loads((ROOT/'r464-config.json').read_text())
steering=base['steering']+'\nLATEST completed r462 adds zero qualified survivors and no denials. 331192 exact coupled recursion for entangled-thread partner counts does not factor competing maximum-initial even-thread connectors into Motzkin products; layered cases are already public. 325688 final-source recurrence specialized at x=1 does not prove membership in the two-variable Q[x,y] contraction ideal; rank/activity-refined fibers or star-deletion elimination remain unpaid, original1306.0294unread. 326360 source right-group branch-star contractions conjugate generators differently across layers; simultaneous compatibility for the SPECIFIED projected Cayley graph is unpaid. Source failure for a different semigroup is not a refutation of this right-zero-factor conjecture. 331491 actual Beke-Csaji-Csikvari-Pituk Advances in Mathematics446(2024)109674 final supplies the public matroid refutation; its printed M direct-sum dual bridge refutes all three displayed inequalities, zero. Do not transfer it to the distinct graphic conjecture. Sixteen reserved original bodies unread;325688final and331491laterrefutation read instead. Specifically identified directed-CSP/snake public solution claims retain unread-proof HOLDs; snippets do not establish them. Root verified178 ownfiles,20original bindings,13frozen inputs. No new mathematical certification or credit.\n'
config=dict(number=465,protected_peers=['expanded-corpus-r463','expanded-corpus-r464'],completed_discovery_numbers=list(range(421,463)),denials=str(denpath),excluded_ids=base['excluded_ids'],excluded_sources=base['excluded_sources'],peer_routing_files=['selection-routing-r463.json','selection-routing-r464.json'],steering=steering)
save(ROOT/'r465-config.json',config)
spec=importlib.util.spec_from_file_location('root_discovery_packet',ROOT/'prepare_discovery_packet.py');module=importlib.util.module_from_spec(spec);spec.loader.exec_module(module);ready=module.prepare(config)
print(json.dumps(dict(accepted_new=57,manifest_files=178,original_bindings=20,frozen_bindings=13,receipt_exit_counts=record['receipt_exit_counts'],new_denials=False,ready=ready)))
