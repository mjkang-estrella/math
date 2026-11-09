"""Root documentary verification/routing; mathematics remains attributed."""
import os,resource
os.sched_setaffinity(0,sorted(os.sched_getaffinity(0))[:2])
resource.setrlimit(resource.RLIMIT_CPU,(120,120));resource.setrlimit(resource.RLIMIT_AS,(6*1024**3,6*1024**3))
from pathlib import Path
import json,hashlib,datetime,collections,re,base64,importlib.util
P=Path(__file__).resolve().parent.parent;ROOT=P/'root-intake-r60';A=P/'expanded-corpus-r467'
def sha(q):return hashlib.sha256(q.read_bytes()).hexdigest()
def dg(b):return hashlib.sha256(b).hexdigest()
def save(q,v):
 assert not q.exists(),str(q)
 q.write_text(json.dumps(v,indent=2)+'\n')
now=datetime.datetime.now(datetime.timezone.utc).isoformat();assert json.loads((P/'ledger.json').read_text())['accepted_new']==57
routing=json.loads((ROOT/'selection-routing-r467.json').read_text());assert sha(A/'TASK.txt')==routing['task_sha256'] and sha(A/'reservation.json')==routing['reservation_sha256']
manifest=json.loads((A/'MANIFEST.json').read_text());entries=manifest['files'];assert len(entries)==132
for n,v in entries.items():
 assert not Path(n).is_absolute() and '..' not in Path(n).parts
 q=A/n;assert not q.is_symlink() and sha(q)==v['sha256'] and q.stat().st_size==v['bytes'],n
exclusions=manifest['terminal_noncircular_exclusions'];assert {str(q.relative_to(A)) for q in A.rglob('*') if q.is_file()}==set(entries)|set(exclusions)
frozen=json.loads((A/'frozen-inputs.json').read_text());assert len(frozen)==13 and all(Path(n).parent==A and sha(Path(n))==h for n,h in frozen.items())
after=json.loads((A/'frozen-after.json').read_text());assert after['count']==13 and after['mismatches']==[]
reservation=json.loads((A/'reservation.json').read_text());ids=reservation['ids'];gates=json.loads((A/'results.json').read_text());prov=json.loads((A/'literal-provenance.json').read_text());assert len(ids)==20 and set(ids)==set(map(int,gates))=={x['id'] for x in prov}
chunks={};sources={}
for row in prov:
 key=str(row['id']);q=Path(row['chunk']);assert q.is_relative_to(P.parent/'lanes/pi-mathdb-full-corpus-inventory-r301/corpus')
 if str(q) not in chunks:
  b=q.read_bytes();chunks[str(q)]=(dg(b),b.splitlines(keepends=True))
 h,lines=chunks[str(q)];assert h==row['chunk_sha256'];raw=lines[row['line']-1]
 assert dg(raw)==row['raw_sha256'] and row['newline']=='LF' and raw.endswith(b'\n') and base64.b64decode(row['raw_b64'],validate=True)==raw
 obj=json.loads(raw);assert obj==row['object'] and obj['mathdb_id']==row['id'];sources[key]=obj['source_url']
 tokens=re.findall(rb'"statement"\s*:\s*("(?:[^"\\]|\\.)*")',raw);assert len(tokens)==len(row['statement_tokens'])==1
 token=tokens[0];v=row['statement_tokens'][0]
 assert base64.b64decode(v['token_b64'],validate=True)==token and dg(token)==v['token_sha256']
 assert json.loads(token)==v['decoded']==obj['statement'] and dg(obj['statement'].encode())==v['decoded_sha256'] and gates[key]['credit']==0
receipts=[]
for q in sorted(A.glob('*.receipt.json')):
 v=json.loads(q.read_text());assert v['cwd']==str(A) and v['cpu_limit_s']==115 and v['as_limit_bytes']==6*1024**3 and v['deadline_s']==130
 receipts.append(dict(path=q.name,sha256=sha(q),exit=v['exit']))
assert json.loads((A/'terminal_manifest.receipt.json').read_text())['exit']==0
budget=json.loads((A/'search-budget.json').read_text());assert budget['calls_used']==3 and budget['queries_used']==9
charges=[json.loads(s) for s in (A/'search-charges.jsonl').read_text().splitlines()];assert len(charges)==3
previous=dict(calls_used=0,queries_used=0,maximum_calls=3,maximum_queries=9,charged_before_call=True)
for i,c in enumerate(charges,1):
 assert c['sequence']==i and c['before']==previous and sha(A/c['plan'])==c['plan_sha256'] and json.loads((A/c['plan']).read_text())['queries']==c['queries']
 expected=dict(previous);expected['calls_used']+=1;expected['queries_used']+=len(c['queries']);assert c['after']==expected;previous=expected
 assert json.loads((A/f"search-{['one','two','three'][i-1]}-response.json").read_text())
assert previous==budget and sha(A/'charge_search.py')==sha(ROOT/'charge_search.py')
events=[json.loads(s) for s in (A/'guard-ledger.jsonl').read_text().splitlines()];counts=collections.Counter(e['event'] for e in events);assert counts==dict(attempt=6,success=6)
for e in events:
 if e['event']=='success':assert sha(A/e['destination'])==e['sha256'] and (A/e['destination']).stat().st_size==e['bytes']
history=json.loads((A/'history-access.json').read_text());assert len(history)==767;forbidden=('formal','code-loop','polynexus','crown','bunkbed','tournament','hat-bipartite')
assert all(not any(token in part.lower() for token in forbidden) for x in history for part in Path(x['path']).relative_to(P).parts)
audit=json.loads((A/'access-audit.json').read_text());assert audit['forbidden_hits']==[] and not audit['embedded_paths_followed'] and not audit['quarantine_evidence_reused']
record=dict(utc=now,source_lane=str(A),manifest_sha256=sha(A/'MANIFEST.json'),verified_manifest_files=132,verified_original_bindings=sorted(ids),verified_frozen_bindings=13,source_url_by_id=sources,routing_pins='Actual task and reservation hashes match retained ROOT genesis',runner_receipts=receipts,receipt_exit_counts=dict(collections.Counter(str(x['exit']) for x in receipts)),guard_events=dict(counts),search_budget=budget,search_counter_continuity='Live old/new states, exact plan digests/querystrings, final counter and immutable helper authenticated; all full saved responses parsed',root_disposition='ZERO_QUALIFIED_SURVIVORS_PUBLIC_STATEMENT_AND_SCOPE_LIMITS_RETAINED',scientific_summary='377054sameTutte/differentintegralcriticalgroup exactgraphwitness missing; Whitney/matroidisomorphic switching preservesboth, source reverse nondetermination nottarget. Rotor prime-nullity/fullsubsetrank matching unpaid; specific searchmentionedpublished diagram actualidentity/proofunreadHOLD.379627actualZhuSun2015Prop2.11PRINTS exact ordinaryNarayana preservation, applicationproofomitted; actualZeng2610.19548v3shiftedstrongcoefficient theorem gives attributed scalarpositive/zero/index0 bridge, namedinternalproofsnotcompletelyaudited. Zero prospectivenovelty; notnewfullprimaryproofaudit.379629Eulerian alln prefixminors/multiplicityrespecting coupling unpaid; row qlogconvex or momentinputs notalllogconvexinput theorem.379052modnversussourcemod4 transcriptioncorrection0.379168actual2006AnnalsCor1.4public withinfiniteextensionproofread, finiteTheorem1.1notfullyaudited.378894literalannouncesMarcusTardosclaim butactualproofunread;378890originalsourcecounterexamplefigureunreadHOLD. Onlythreereservedoriginalworks acquiredcoveringfourIDs;sixteenassignedexactoriginalarxivbodiesunread;otherthreepayloadscomparisonworks.',all20_gates=gates,new_denials=False,history_access_audit=dict(saved_records=767,protected_component_matches=0,scope='Ownsavedaccessinventory only; no historical externalpathfollow byroot'),process='No reported localfailedinvocations or sourceunavailability; savedfullcappedoutputs and materialrecoveries retained. No figures visuallyinspected, figuredependentclaimsheld. Bounded source/read/priority limits remain; sampled/native/writerpeaks unavailable, no universalcompliance claim.',root_scope='Documentary integrity/provenance/routing only; no root mathematical solving/programs/Lean/checkers or protected externalpathfollow',credit=0,accepted_new=57,target_new=60,formal_dispatch=False,terminal_self_exclusions=exclusions)
save(P/'expanded-corpus-r467-parent-integration.json',record)
den=json.loads((ROOT/'inherited-denials-r470.json').read_text());den['utc']=now
den['root_r467_scope']='No newdenials.377054sameTutte/differentcritical witness/fullsubsetrank andprime-nullity unpaid, actualpublished-diagramclaim unreadHOLD.379627actualZhuSun2015Prop2.11printed exactNarayana preservation proofomitted, actualZengshiftedbridge/index0/zero/scalar cases attributed/notfullinternalproofaudit,0prospectivenovelty.379629allnEulerianprefix/coupling unpaid, rowqlogconvexitynotallinputpreservation.379052moduluscorrection0,379168actualAnnals2006Cor1.4public0withfiniteTh1.1notfullyaudited.132ownmanifest20rawtokenbindings13frozenverified,6GETsuccess3search9queries;767ownsavedaccessrecords no protectedcomponents. No qualifiedsurvivor or credit.'
denpath=ROOT/'inherited-denials-r471.json';save(denpath,den)
base=json.loads((ROOT/'r470-config.json').read_text());steering=base['steering']+'\nLATESTr467completedzero:377054 exactsameTutte/differentintegralcriticalgraph pair still missing; Whitney/matroidisomorphic switching preservesboth, reverse non-determination example is NOTtarget. Search-mentioned publisheddiagram identity/proof remains preciseHOLD, notauthenticatedwitness.379627actualZhuSun2015Prop2.11 prints ordinaryNarayana preservation but omits itsapplicationproof; actualZeng2610.19548v3 shifted theorem gives attributed scalar/zero/index0 conversion, internalproofbodiesnotfullyaudited. Zero prospective novelty, notclaimed new full proof or independentaudit.379629rowEulerianqlogconvexity/momentinputs do NOT settle all logconvex scalarinputs; alln prefixminor or multiplicitycoupling lemma unpaid.379052modnversussourcemod4 istranscriptioncorrection0.379168actualAnnals2006Cor1.4public/infiniteextensionproofread, finiteTh1.1notfullyaudited.378894literalpublicMarcusTardosclaim and378890sourcecounterexamplefigure remain actualbodyHOLDs. Threeoriginalworks acquired coveringfourIDs; sixteenexact originalarxivbodiesunread. SixGETsuccess,3search9queries,no newdenials;132ownfiles20originalbindings13frozenverified; own767historyrecords no protectedcomponents.57/60unchanged.\n'
config=dict(base);config.update(number=471,protected_peers=['expanded-corpus-r469','expanded-corpus-r470'],peer_routing_files=['selection-routing-r469.json','selection-routing-r470.json'],completed_discovery_numbers=sorted(set(base['completed_discovery_numbers'])|{467}),denials=str(denpath),steering=steering,year_floor=2000,candidate_pool=400)
save(ROOT/'r471-config.json',config)
spec=importlib.util.spec_from_file_location('root_discovery_packet',ROOT/'prepare_discovery_packet.py');module=importlib.util.module_from_spec(spec);spec.loader.exec_module(module);ready=module.prepare(config)
allow=json.loads((Path(ready['lane'])/'historical-results-allowlist.json').read_text());assert all(not any(token in part.lower() for token in forbidden) for name in allow for part in Path(name).relative_to(P).parts)
assert all('expanded-corpus-r463' not in name and 'expanded-corpus-r466' not in name for name in allow)
print(json.dumps(dict(accepted_new=57,manifest_files=132,original_bindings=20,frozen_bindings=13,receipt_exit_counts=record['receipt_exit_counts'],new_denials=False,ready=ready,history_filter='Actualallowlist andcompletedownaccessinventory no protected pathcomponents')))
