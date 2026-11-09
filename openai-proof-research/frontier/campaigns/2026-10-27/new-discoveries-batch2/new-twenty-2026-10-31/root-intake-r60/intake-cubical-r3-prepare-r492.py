"""Root documentary integrity, bounded significant-credit disposition and disjoint routing; no mathematics."""
import os,resource
os.sched_setaffinity(0,sorted(os.sched_getaffinity(0))[:2]);resource.setrlimit(resource.RLIMIT_CPU,(120,120));resource.setrlimit(resource.RLIMIT_AS,(6*1024**3,6*1024**3))
from pathlib import Path
import json,hashlib,datetime,collections,importlib.util
P=Path(__file__).resolve().parent.parent;ROOT=P/'root-intake-r60';A=P/'cubical-zigzag-final-primary-sol-r3'
def sha(q):return hashlib.sha256(q.read_bytes()).hexdigest()
def read(q):return json.loads(q.read_text())
def save(q,d):
 assert not q.exists(),str(q)
 q.write_text(json.dumps(d,indent=2)+'\n')
now=datetime.datetime.now(datetime.timezone.utc).isoformat();assert read(P/'ledger.json')['accepted_new']==57
ready0=read(ROOT/'cubical-final-primary-r3-ready.json');assert sha(A/'TASK.txt')==ready0['task_sha256']
m=read(A/'hash-manifest.json');files={v['path']:v for v in m['files']};assert len(files)==len(m['files'])==101
for n,v in files.items():
 assert not Path(n).is_absolute() and '..' not in Path(n).parts
 q=A/n;assert not q.is_symlink() and sha(q)==v['sha256'] and q.stat().st_size==v['bytes'],n
ex=m['terminal_noncircular_exclusions'];assert set(ex)=={'hash-manifest.json','seal_manifest.receipt.json','seal_manifest.output.txt'}
actual=set()
for q in A.rglob('*'):
 assert not q.is_symlink()
 if q.is_file():actual.add(str(q.relative_to(A)))
assert actual==set(files)|set(ex)
frozen=read(A/'frozen-inputs.json');assert len(frozen)==34
for n,h in frozen.items():assert Path(n).is_relative_to(A) and sha(Path(n))==h
before=read(A/'frozen-before.json');after=read(A/'frozen-after.json');assert before['count']==after['count']==34 and before['mismatches']==after['mismatches']==[]
receipts=[]
for q in sorted(A.glob('*.receipt.json')):
 v=read(q);assert v['cwd']==str(A) and v['cpu_limit_s']==115 and v['as_limit_bytes']==6*1024**3 and v['group_rss_guard_bytes']==6*1024**3 and v['deadline_s']==130 and len(v['affinity'])<=2 and v['killed'] is None
 receipts.append(dict(path=q.name,sha256=sha(q),exit=v['exit']))
assert read(A/'seal_manifest.receipt.json')['exit']==0
budget=read(A/'search-budget.json');assert budget==dict(calls_used=1,queries_used=3,maximum_calls=1,maximum_queries=3,charged_before_call=True)
charges=[json.loads(s) for s in (A/'search-charges.jsonl').read_text().splitlines()];assert len(charges)==1;c=charges[0]
assert c['before']==dict(calls_used=0,queries_used=0,maximum_calls=1,maximum_queries=3,charged_before_call=True) and c['after']==budget and c['sequence']==1 and sha(A/c['plan'])==c['plan_sha256'] and read(A/c['plan'])['queries']==c['queries'] and len(c['queries'])==3
assert isinstance(read(A/'current-search-response.json'),str) and sha(A/'charge_search.py')==sha(ROOT/'charge_search.py') and not (A/'guard-ledger.jsonl').exists()
gates=read(A/'review.json');g=gates['378413'];assert g['credit']==0 and g['new_GET_hops']==0 and g['parent_total_GET_hops']==4 and g['parent_total_search_calls']==2 and g['parent_total_search_queries']==6
assert sha(A/'inputs/williams.pdf')=='01c22ffa380fcb3318091e19c8de590a9043602dc4a27fd05d4c3c950a14b03a'
assert (A/'GLYPH-CORRECTION.md').is_file() and (A/'REVIEW-pre-glyph-correction.md').is_file()
record=dict(utc=now,mathdb_id=378413,source_lane=str(A),task_genesis_verified=True,manifest_sha256=sha(A/'hash-manifest.json'),review_sha256=sha(A/'REVIEW.md'),verified_manifest_files=101,verified_frozen_bindings=34,runner_receipts=receipts,receipt_exit_counts=dict(collections.Counter(str(x['exit']) for x in receipts)),new_GET_hops=0,parent_total_GET_hops=4,new_search_calls=1,new_search_queries=3,parent_total_search_calls=2,parent_total_search_queries=6,search_budget=budget,keyed_review=gates,root_disposition='EXCLUDE_PROPOSED_FAMILY_FROM_SIGNIFICANT_DISCOVERY_CREDIT_ROUTINE_FOLDING_APPLICATION',
 ordinary='IndependentR1fullordinary/literalrefutationPASSretained. NewlyauthoredR3finitefoldingapplicationisNOTaseparatelyindependentreviewedcertificate;rootdoesnotgrantnewmathematical/formalPASSoracceptance. No rootmathematicalsolving/programs/Lean/checkers.',
 significance='Rootadoptszero-significant-discovery-creditroutinefoldingapplicationdispositionbasedonactualoriginalProposition4.7andexplicitapplicationdata. Reviewercompletesfiniteintermediatelatticeincludingg2,facefreeinducedinvolution/localthinness,distinctcompatibleorientedorbits,twofullflagincidencesandpositivefoldedtypeIcount. Actualsourcestatesexchangedzigzagfoldingaddsonehalfintersectionandmentionstorus-to-Kleinbottle. Thisisthecompleteconcretemechanism-basedobjection,notshortness/nonorientabilityalone/claimWilliamsprintedexactwitness. Strongpositiveproperfinite3dimcounterexampleandnontrivialapplicationdetailsretained;noearlierexactprintedwitnessclaimed.',
 source='Original0405279v1scopePASSretained;actual2005SABM29(2)301-320final/correctionsHOLD,noprimarybodyURLobserved,NOoriginalworkdeliveryfailure/newban. Cachedv1May2004/2018displaydatenotfinalequivalence. OriginalProposition4.7hasno separateproofparagraph;reviewerprovidesflag-incidenceconversiondirectly. Rootpersonallyreadactualcachedproposition/examplesasdocumentarycomparison. Earlierreportunprimedglyphmistakecorrectedfromoriginalp4primeonf_1,j,oldreportpreserved;argumentusesunambiguoussigma1self-definitionnottypo.',
 Williams='ActualcompleteWilliamsPetrieSchemesCJM57(4)(2005)844-870bodyreadandidentity/DOI10.4153/CJM-2005-033-6authenticatedbyreviewer. Boundedtheorem-levelNONMATCH: acoptic/Petrialschemeclassification/Coxeterhoneycomb/geometrypolyhedra/productpolygonsresultsnotoldcubicalsigma1signaturecertificate. No worldwideabsenceorindependentcomputationaltablesauditclaimed.',
 prior='Originalfoldingmechanismfullapplicationisbasisofzero-creditdisposition,notmatchingexactpriorwitness. Blockedcompanion1509.03754finalboundedlimit,notinventedmatchingcounterclaim;cachedv3narrowsimplicialz-simplicitynottransferoldsignature. Genericbook/unidentifiedlengthsleadnotworldwidenoveltyveto.',
 process='101ownfiles34frozenverified,0newGET,parent4/8hops;1newsearch3queries,parent2/2calls6/6strings,nonewdenials/nobudgetreset. Fullsearchresponse/continuityverified,nofourregistryrootreconstruction. Materialglypherrorandcorrection/bothreportsretained;fivepermittednativeownimagepresentationsdeclaredunknownresourcepeaks,nouniversalprocedurePASS. R1displayqualification/R2guardSTOPandpermanentr395/r463/r466/r482quarantinesunchanged,no retry/recovery. Allwriter/native/supervisorlimitsretained.',
 family='Oneglide/cube/period/dimension/signaturefamily,57+39boundedscopenonmatchinherited,nocertificateaudit. Source/domain/helper/formalization/parameter/correctioncredit0.',
 terminal_self_exclusions=ex,root_scope='Documentaryintegrity/creditdisposition/routingonly;no root mathematicalwork.',credit=0,accepted_new=57,total=96,formal_dispatch=False)
delta='Completedcubical378413r3qualification:WilliamscompleteactualCJM57(2005)844-870body/DOI10.4153/CJM-2005-033-6authenticated,boundedtheoremNONMATCHnotoldtypeIsignature. RootEXCLUDEproposedfamilyfromsignificantcreditascompleteoriginalProposition4.7foldingapplication:finiteintermediatelatticeincludingg2,facefreeinvolution/compatibleorbitdistinction/twoflagincidences/positivefoldedtypeIbridgepaidbyreviewer. Newapplicationauthornotseparateindependentcertificate;priorR1ordinary/literalPASSretained,noacceptance/mathPASSgranted. Notshortness/nonorientabilityalone/notclaimWilliamsexactwitness. Original2005final/correctionHOLD,noobservedprimarybodyURL/nodeliveryattempt/NOneworiginalworkban. Materialp4primeglyphmisreadcorrected,oldreportpreserved;actualsigma1self-definitionusednottypo.101files34frozen0newGET1search3queries,parenttotal4GET2search6stringsverified,nonewdenials/budgetreset. R1/R2processlimitsretained. Noformaldispatch/credit,57/60unchanged.'
den=read(ROOT/'inherited-denials-r500.json');den['utc']=now;den['root_cubical378413_qualification_r3_scope']=delta;denpath=ROOT/'inherited-denials-r501.json'
# All verification precedes root integrations/new discovery construction.
save(P/'cubical-zigzag-final-parent-integration-sol-r3.json',record);save(denpath,den)
config=read(ROOT/'r491-config.json');config.update(number=492,protected_peers=['expanded-corpus-r491','pagerank-uniform-source-review-sol-r1'],peer_routing_files=['selection-routing-r491.json','selection-routing-pagerank-uniform-review-r1.json'],denials=str(denpath),year_floor=2000,candidate_pool=400,quarantined_discovery_numbers=[395,463,466,482])
config['completed_discovery_numbers']=sorted(set(config['completed_discovery_numbers'])|{490})
config['excluded_ids']=sorted(set(config['excluded_ids'])|{316846,317603,378413})
config['excluded_sources']=sorted(set(config['excluded_sources'])|{'https://arxiv.org/abs/0711.2867','https://arxiv.org/abs/0808.0774','https://arxiv.org/abs/math/0405279','https://arxiv.org/abs/1509.03754'})
config['steering']+='\n'+den['root_cubical378413_qualification_r2_scope']+'\n'+den['root_r490_scope']+'\n'+delta+'\n';save(ROOT/'r492-config.json',config)
spec=importlib.util.spec_from_file_location('discovery_constructor',ROOT/'prepare_discovery_packet.py');module=importlib.util.module_from_spec(spec);spec.loader.exec_module(module);ready=module.prepare(config)
allow=read(Path(ready['lane'])/'historical-results-allowlist.json');forbidden=('formal','code-loop','code_loop','polynexus','crown','bunkbed','tournament','hat-bipartite')
for name in allow:
 rel=Path(name).relative_to(P)
 assert not any(t in part.lower() for part in rel.parts for t in forbidden)
 assert not any(part in {f'expanded-corpus-r{x}' for x in [395,463,466,482]}|{f'expanded-corpus-r{x}-parent-integration.json' for x in [395,463,466,482]} for part in rel.parts)
save(ROOT/'cubical-r3-completion-boundary-delta.json',dict(utc=now,message=delta,new_protected_peer='expanded-corpus-r492',immutable_worker_inputs_unchanged=True))
print(json.dumps(dict(files=101,frozen=34,receipt_exit_counts=record['receipt_exit_counts'],disposition=record['root_disposition'],ready=ready,accepted_new=57,credit=0)))
