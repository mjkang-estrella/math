"""Root documentary intake of independent review; no mathematical execution."""
import os,resource
os.sched_setaffinity(0,sorted(os.sched_getaffinity(0))[:2])
resource.setrlimit(resource.RLIMIT_CPU,(120,120));resource.setrlimit(resource.RLIMIT_AS,(6*1024**3,6*1024**3))
from pathlib import Path
import json,hashlib,datetime,collections,importlib.util
P=Path(__file__).resolve().parent.parent;ROOT=P/'root-intake-r60';A=P/'percolation-hub-source-review-sol-r1'
def sha(q):return hashlib.sha256(q.read_bytes()).hexdigest()
def save(q,v):
 assert not q.exists(),str(q)
 q.write_text(json.dumps(v,indent=2)+'\n')
now=datetime.datetime.now(datetime.timezone.utc).isoformat();assert json.loads((P/'ledger.json').read_text())['accepted_new']==57
ready0=json.loads((ROOT/'percolation-review-r1-ready.json').read_text());assert sha(A/'TASK.txt')==ready0['task_sha256']
manifest=json.loads((A/'BYTE-MANIFEST.json').read_text());entries={x['path']:x for x in manifest['files']};assert len(entries)==108
for n,v in entries.items():
 assert not Path(n).is_absolute() and '..' not in Path(n).parts
 q=A/n;assert not q.is_symlink() and sha(q)==v['sha256'] and q.stat().st_size==v['bytes'],n
exclusions=manifest['terminal_noncircular_exclusions']
assert {str(q.relative_to(A)) for q in A.rglob('*') if q.is_file()}==set(entries)|set(exclusions)
frozen=json.loads((A/'frozen-inputs.json').read_text());assert len(frozen)==25 and all(Path(n).is_relative_to(A) and sha(Path(n))==h for n,h in frozen.items())
after=json.loads((A/'frozen-after.json').read_text());assert after['count']==25 and after['mismatches']==[]
receipts=[]
for q in sorted(A.glob('*.receipt.json')):
 v=json.loads(q.read_text());assert v['cwd']==str(A) and v['cpu_limit_s']==115 and v['as_limit_bytes']==6*1024**3 and v['deadline_s']==130
 receipts.append(dict(path=q.name,sha256=sha(q),exit=v['exit']))
assert json.loads((A/'seal-manifest.receipt.json').read_text())['exit']==0
budget=json.loads((A/'search-budget.json').read_text());assert budget['calls_used']==0 and budget['queries_used']==0 and budget['maximum_calls']==2 and budget['maximum_queries']==6
assert not (A/'search-charges.jsonl').exists() and sha(A/'charge_search.py')==sha(ROOT/'charge_search.py')
events=[json.loads(s) for s in (A/'guard-ledger.jsonl').read_text().splitlines()];counts=collections.Counter(e['event'] for e in events);assert counts==dict(attempt=3,success=3)
for e in events:
 if e['event']=='success':assert sha(A/e['destination'])==e['sha256'] and (A/e['destination']).stat().st_size==e['bytes']
keyed=json.loads((A/'keyedreview.json').read_text());assert set(keyed)=={'330008'};g=keyed['330008'];assert g['credit']==0 and not g['qualified_survivor'] and not g['formal_dispatch'] and g['disposition']=='HOLD_SOURCE_SCOPE_AND_SIGNIFICANCE'
record=dict(utc=now,mathdb_id=330008,source_lane=str(A),review_sha256=sha(A/'REVIEW.md'),gap_sha256=sha(A/'GAP.md'),manifest_sha256=sha(A/'BYTE-MANIFEST.json'),verified_manifest_files=108,verified_frozen_bindings=25,task_genesis_verified=True,runner_receipts=receipts,receipt_exit_counts=dict(collections.Counter(str(x['exit']) for x in receipts)),guard_events=dict(counts),search_budget=budget,new_denials=False,root_disposition='PARK_SOURCE_QUANTIFIERS_AND_SUBSTANTIVE_SCOPE_NOT_GENERIC_UNKNOWN',ordinary='IndependentfinitefamilyPASS:bidirectedtriangleplusmpendantleavesrho1, fixedp1/2,positivefractionSCCthreshold. Siteexistenceprobabilityboundedbelowbutnotwhp;conditionaluniquenesscertain. Undirectedbond andindependentdirectedarc SCCexistence/uniquenesswhp paidseparately. No infinite locallyfinitecounterexample. Allhub/model/spectralhelpers onefamily.',source='Actual1503.00410v1siteversusliteralbond discrepancy and undefinedfinitegraphsequence/cluster/conditionalwhp remain. OLGstrongconnectivity notsilentlyinserted asstandingConjecture2hypothesis. Hubunionnotlocallyfinite. No invented exactLeannegation forambiguousendpoint.',prior='Specific1610.04897bodyfullyread, HOLDdischarged: actualfiniteTh3 requires boundedroutefromeveryarctoinverse, pendantarcsfail; actualTh4/5 infinite locallyfinite. Completeactual1505.03963v5Th12+20+24/Cor25 source-to-intendedINFINITEbridgepaid, notfinitewhpbridge. No authenticatedfinitehubprior orcompleteroutineexclusion; no specificallyapplicableunreadproof remains aftercomparison.',significance='HOLD genuinefiniteobstruction versus omitted-limit/domainrepair unresolved; no acceptedfullintendedtarget. Root retains precise scopegate,notgenericworldwidenoveltyveto or shortness-based exclusion. No formal or freshretrievalfollowup without concrete newscope evidence.',current_version_limits='Threeactualguarded acquisitions:1610.04897v1body pluscurrentarxivrecords for1610.04897and1505.03963. Records identifyv1/v5 respectively; nojournal/correctionidentified bythoseboundedrecords.2018Elsevierfooter isnotproof ofpublication. No universalfinalabsence claim.',family='Reviewer personallycompared frozen57+39trustedscopes, boundednonoverlap, no oldcertificateaudit.',process='Preserved one documentaryKeyError onprior39schema and changedrecovery; fullmaterialdenial/proof/scope truncations recovered. Frozenowncopiesonly,nohistoricalpaths. Sampled/native/writerpeak limitations retained; no universalcompliance claim.',review=g,root_scope='Documentary integrity and acceptance/routing adjudication only; no root mathematical solving/programs/Lean/checkers',credit=0,accepted_new=57,target_new=60,formal_dispatch=False,terminal_self_exclusions=exclusions)
save(P/'percolation-hub-source-parent-integration-sol-r1.json',record)
den=json.loads((ROOT/'inherited-denials-r467.json').read_text());den['utc']=now
den['root_percolation330008_independent_scope']='IndependentfinitehubfamilyordinaryPASS; siteconditional versusbondwhp modelsseparatelypaid. SCIENTIFICPARK literalundefinedfiniteasymptotics/graphsequence/clusterquantifiers and finiteobstructionversusomittedlocallyfiniteinfinite-domaincorrection. Specific1610.04897actual2pagev1bodyread: finiteTh3pendantarcroutenoninclusion boundednonmatch; infiniteTh5 andcomplete1505.03963v5Th12+20+24Cor25 intendedINFINITEbridgepaid. No matchingunreadpriorproofstillidentified, no completeroutineexclusion, no infinitecounterexample. No newdenials/zero searches;108ownmanifest25frozen3GETsuccess. No formal or credit.'
denpath=ROOT/'inherited-denials-r469.json';save(denpath,den)
base=json.loads((ROOT/'r468-config.json').read_text())
steering=base['steering']+'\nLATEST330008independentreviewCOMPLETED/PARK,notactive: finitehubrho1/siteconditional andtwo bondwhp giantuniqueness arguments independentordinaryPASS, but no infinite locallyfinite counterexample. Actual1610.04897v1 full2pagebodycomparison is now PAID, do notretain an unread-primary HOLD: finiteTh3requires inverse-arc routes absent atpendants; infiniteTh5 locallyfinite. Actual1505.03963v5Th12+20+24/Cor25 supplies complete public intended-INFINITE uniqueness bridge, notfiniteconditionalwhp. Source1503.00410v1siteversusliteralbond and undefined finitegraphsequence/macroscopiccluster/conditionalwhp quantifiers remain exact scientificscope gaps. No specificallyapplicableunreadproof remains identified aftercomparison. No authenticatedfinitehubprior/routineexclusion, no shortness-based rejection, no worldnoveltyclaim. RootPARK is substantivefinite-versusomittedlimit/domainrepair, notgenericunknown. No formal or freshretrievalfollowup withoutconcrete newscope evidence. Allhubvariants/modelhelpers onefamily.3GETsuccess/0search,108ownfiles25frozenverified;57/60unchanged.\n'
config=dict(base);config.update(number=469,protected_peers=['expanded-corpus-r467','expanded-corpus-r468'],peer_routing_files=['selection-routing-r467.json','selection-routing-r468.json'],denials=str(denpath),steering=steering,year_floor=2000,candidate_pool=400)
save(ROOT/'r469-config.json',config)
spec=importlib.util.spec_from_file_location('root_discovery_packet',ROOT/'prepare_discovery_packet.py');module=importlib.util.module_from_spec(spec);spec.loader.exec_module(module);ready=module.prepare(config)
allow=json.loads((Path(ready['lane'])/'historical-results-allowlist.json').read_text());forbidden=('formal','code-loop','polynexus','crown','bunkbed','tournament','hat-bipartite')
assert all(not any(token in part.lower() for token in forbidden) for name in allow for part in Path(name).relative_to(P).parts)
assert all('expanded-corpus-r463' not in name and 'expanded-corpus-r466' not in name for name in allow)
print(json.dumps(dict(accepted_new=57,manifest_files=108,frozen_bindings=25,receipt_exit_counts=record['receipt_exit_counts'],review_disposition=record['root_disposition'],ready=ready,history_filter='No protected basename/component or quarantined history in actual allowlist')))
