"""Prepare sealed-baseline continuation and disjoint discovery metadata; no root maths."""
import os,resource
os.sched_setaffinity(0,sorted(os.sched_getaffinity(0))[:2])
resource.setrlimit(resource.RLIMIT_CPU,(120,120))
resource.setrlimit(resource.RLIMIT_AS,(6*1024**3,6*1024**3))
from pathlib import Path
import json,hashlib,datetime,shutil,importlib.util
ROOT=Path(__file__).resolve().parent;P=ROOT.parent;F=P/'high-girth-ur-matching-formal-sol-r3';L=P/'high-girth-ur-matching-formal-sol-r4'
def read(p):return json.loads(p.read_text())
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def save(p,v):
 assert not p.exists(),str(p)
 p.write_text(json.dumps(v,indent=2)+'\n')
now=datetime.datetime.now(datetime.timezone.utc).isoformat();assert read(P/'ledger.json')['accepted_new']==57
report=read(ROOT/'formal-r3-r512-product-r2-intake-report.json');assert report['no_root_mathematics']
parent=read(P/'high-girth-ur-matching-formal-parent-integration-r3.json');assert parent['verified_manifest_files']==213 and len(parent['green_modules'])==4
assert not L.exists() and not (P/'expanded-corpus-r513').exists() and not (P/'expanded-corpus-r514').exists()
L.mkdir();origins={}
def copy(src,rel):
 dst=L/rel;dst.parent.mkdir(parents=True,exist_ok=True);shutil.copyfile(src,dst);assert sha(src)==sha(dst);origins[rel]=dict(path=str(src),sha256=sha(src))
for h in ['bootstrap.py','run.py','write_lane.py','verify_frozen.py','model-policy-sol-only.json','PINS.json','formal_command.py','check.sh','checker.sh']:copy(F/h,h)
for h in ['check.sh','checker.sh']:(L/h).chmod(0o755)
for d in ['src','build','cache','audit','receipt','logs','results','cleanroom/src','cleanroom/build','manuscript','output/pdf']:(L/d).mkdir(parents=True,exist_ok=True)
for q in (F/'inputs').rglob('*'):
 if q.is_file():
  rel=Path('inputs')/q.relative_to(F/'inputs')
  if str(rel)=='inputs/ROOT-AUTHORIZATION.json':rel=Path('inputs/PREVIOUS-ROOT-AUTHORIZATION.json')
  elif str(rel)=='inputs/INHERITED-DENIALS.json':continue
  copy(q,str(rel))
copy(ROOT/'inherited-denials-r526.json','inputs/INHERITED-DENIALS.json')
baseline=[]
for row in parent['green_modules']:
 module=row['module'];copy(F/'src'/(module+'.lean'),'src/'+module+'.lean')
 blobs=[]
 for q in (F/'build').glob(module+'.*'):
  if q.is_file():copy(q,'build/'+q.name);blobs.append(dict(path='build/'+q.name,sha256=sha(q)))
 assert sha(L/'src'/(module+'.lean'))==row['source_sha256'] and sha(L/'build'/(module+'.olean'))==row['olean_sha256']
 baseline.append(dict(row,blobs=blobs))
for name in ['URMatchingSource.lean','URMatchingBodyInventory.lean','URMatchingAxioms.lean','URMatchingNegativeLoop.lean']:copy(F/'src'/name,'inputs/drafts/'+name)
labels=set()
for row in parent['green_modules']:labels.update([row['compile'],row['checker']])
labels.update(['pin_scope_05','axioms_40','partial_replay_50','inventory_typed_47','negative_loop_54'])
for q in F.glob('*.receipt.json'):
 if read(q)['exit']!=0:labels.add(q.name[:-len('.receipt.json')])
for label in sorted(labels):
 for suffix in ['.receipt.json','.output.txt']:copy(F/(label+suffix),'inputs/previous-receipts/'+label+suffix)
for name in ['SUMMARY.md','CHECKPOINT.md','results/338806.json','source-to-literal-map.json','evidence/receipt-inventory-checkpoint.json']:copy(F/name,'inputs/previous/'+Path(name).name)
copy(F/'evidence/first-model.lean.txt','inputs/previous/first-model.lean.txt')
save(L/'BASELINE.json',dict(origin=str(F),root_verified_manifest_sha256=parent['manifest_sha256'],immutable_green_modules=baseline,uncompiled_drafts='inputs/drafts only; NOT paid theorem/source endpoint',rule='Own copied baseline source+all compiler sidecars immutable; do not rewrite/recompile these in production. Import ownbuild sealed oleans. Final empty-build source-only replay must rebuild copied source plus new source with no production/legacy paths. No external origin paths may be followed.'))
authorization=dict(utc=now,mathdb_id=338806,status='CONTINUE_UNCOUNTED_FORMAL_RESEARCH_INCOMPLETE_SCIENTIFIC_HOLD_PRESERVED',authority='Continuation of existing user-authorized literal Lean research; no additional acceptance or scientific waiver.',previous_authorization=str(P/'high-girth-ur-matching-formal-research-authorization-r3.json'),basis='Root documentary verification confirms four strict/kernel green modules and only three-module partial replay. No literal refutation exists; full body audit failed. Continue actual unpaid mathematical pipeline without repeating green baseline.',scientific_status='HOLD remains; final/prior/significance can veto credit. No published proof/prior clearance/source-access waiver implied by formal progress.',paid=[x['module'] for x in baseline],unpaid=parent['result']['unpaid'],credit=0,accepted_new=57,target_new=60,root_Lean_or_math_execution=False)
save(P/'high-girth-ur-matching-formal-research-authorization-r4.json',authorization);save(L/'inputs/ROOT-AUTHORIZATION.json',authorization)
task=(F/'TASK.txt').read_text().replace(str(F),str(L)).replace('product-measure-dimension-source-review-sol-r1','expanded-corpus-r513').replace('expanded-corpus-r512','expanded-corpus-r514')
override=f'''R4 CONTINUATION OVERRIDE — ONLY GPT-6.1 Sol HIGH/DEFAULT,NOCHILDREN,offline uncredited research. ScientificHOLD/credit0/57of60 unchanged. This override supersedes earlier R3 first-new-proof/base-writing and baseline-replay instructions in inherited TASK below; every other source/model/cap/audit/replay/acceptance restriction remains. Full literal endpoint is STILL unpaid; do not stop at another model/control milestone.

FIRST command EXACTLY timeout 20 python3 -I -B {L}/bootstrap.py
SECOND command EXACTLY timeout 140 python3 -I -B {L}/verify_frozen.py before
Then only own immutable cappedrun/writer/wrappers. Activepeers expanded-corpus-r513 andexpanded-corpus-r514 ENTIRELYprotectedincludingmetadata/stat/hash/list/glob/poll/reservations/flatintegrations. Originalr3 andallotherlanes nowexternal/protected,evenbaseline origin paths: OWN COPIES ONLY plus pinnedupstreamAPIs. No network/sourcequeries/git/install/account/browser/othermodels/mathprograms/solvers/shared/tmpwrites/backgroundjobs. PINS/helpers/baselineFROZEN,neveroverwrite. Externaloriginstringsprovenanceonly.

Read BASELINE.json, inputs/ROOT-AUTHORIZATION.json, previousSUMMARY/CHECKPOINT/result/source-map, selected actualfailed/successfulreceipts andauthor/independentproofs. Fourownbaseline modules Base/Finite/Deletion/Controls and ALL ownbuildcompiler sidecars are IMMUTABLE. Root verified their actual strictcompile/checker hashes andreceipts. Do NOT rewriteorunchangedrecompilethem,do not runcheck.sh onthese frozenbaseline names. Use ownbuildsealedbaseline imports; noexternalr3LEAN_PATH/import/source reads. Finalcleanroomreplay mustfreshbuild ALL baselineSOURCE plusnewmodules, fromEMPTYownnewbuild/upstreamonly,no production/legacy/author paths. Ifgenuinebaselinefidelityerror arises, discloseprecisely; addnewfaithfuldefinitions/provedgenericbridgesasneededwithoutmutatingfrozenbaseline orassumingendpoint.

FIRST NEW-PROOF work aftermandatoryread/pincheck MUST advanceanUNPAIDrealmodule: write/complete actualUR directed-cycle switch andDAG emptyrectangle proof, or prerequisite faithfulsource/girthmodule from frozeninputs/drafts/URMatchingSource.lean if needed, andimmediatelystrictcompile/kernelcheckit BEFORE broadAPI/planningtours. TheSource draft waswrittenbutNEVERcertified,sofirstrealcompile isnotastale rerun. Drafts/Axioms/BodyInventory/NegativeLoop are INPUTS,notpaidproofs. Neweditablefiles ONLYsrc/newmodule names,authoredthroughwriter. No rebuildingtheoldfirstmodel/no controls-only stopping. Diagnostic-drivenpinnedAPIlookupallowedafterrealnewproofwrite/compile; preserveeveryfailuretrueexit.

PRIORITIZE unpaid CORE MATHEMATICS in ordinary proof order: URmatchingdirectedcycleproducesdifferentmatchingwithsamecoveredvertices;topologicalemptyrectangle;finite100independentpermutationno-holecount;shortcoloredcycle/parallelwitnessfirst-momentbound;finiteMarkov/unionexistenceforallg;induceddeletion/noholes/degree/girth/relabeling/matchingretention;strictrealratioandUNIVERSALliteralnegation. ExistingDeletion onlyoriginalgraphlostedgecardinality,NOTinduced/relabeltransport. ExistingBase/Finitefaithfulmodelmaxima,notfiniteexistenceaxiom. GenuineWalk.IsCycle/forest/sourcebridge andallfinite-type/relabeling bridge stillUNPAID. Follow copiedcompleteindependentPROOF,notinventedweakenedquestion. No assumedgoodtuple/noholes/expander/probabilityexistence/conclusion-bearingpremises/finiteenumerationanswerencoding.

AUDIT failure inventory_typed_47 actualLean-6/runner250 threadcreationalreadyhad-j1,LEAN_NUM_THREADS1,M3500; doNOTclaim missingflagorunchangedretry. Keepallfailedimport/header/type/auditreceipts. NEWMATHEMATICSFIRST; fullbodyauditafterendpoint via shardedproduction-declaration/reachableclosure traversal avoidinggiantenvironment/bodymaterialization andunneededimports. EveryLean/auditprocess-j1,-M3500 orstricter,envLEAN_NUM_THREADS1,sameAS6GiB/RSS6GiB/CPU115caps; no limitincrease. Scoped23-declarationaxiomprint isNOTfullbodyaudit; three-module6exit0replay isNOTfullendpoint/controlreplay. Actualorigin/closure/unsafe/private/generatedmetadata auditstillrequired,withupstreamtrustlimitscandid; no unsupported importedproof-body claim. Negative-loop exit1 wasintentional,notproductionPASS.

PIN verification priorr3actualruntime4.34.1/binaryhashes andmathlibdetachedHEADd13f23b723b8a846827a245b89c10fc7d3f11612 matched. Verifycurrentavailablemetadata undercapsonly,no gitbinary/network. PINSunchanged; recordlimitsseparately. All oldversion/resourcefailuresretained; resourcepeaksnative/transient/writer/supervisorunknown. Everynewgreenmodulecompile+checker+scopedaxioms+checkpoint exactsource/olean/log/receipt hashes; nofuturetense handback. Ifinterrupted,persistactualnewmathsources,lastrealdiagnosticsandpreciseunpaidledger. Continue fullpipeline,notselfdeclarecompleteonhelper.

Themanuscript/fullPDF/fullbodyaudits/controls/fullsourceonlyreplay/fullsource-fidelityreview/independentreview/rootscientificadjudicationareUNPAID. No paper existedr3;no misleadingreuseclaim. ScientificHOLDmustbeexplicitinresults/manuscript,source1803.11032/finalDOI closednonewdeliveries. FinaltechnicalPASSonlyafteractualendpoint/allbridges/replay/audits; acceptance/creditstillROOTONLYandmayberefused. SealstandaloneafterfrozenTHENexhaustiveOWNbytesincludingbaseline sidecars/newsource/allcompletedreceipts/inputs/paper/audits,exactterminalnoncircularexclusions,neverexternalfrozenmaps. Credit0/57unchanged.

INHERITED FULL TASK (overrideabovecontrolsallconflicts):
'''
(L/'TASK.txt').write_text(override+task)
save(L/'INPUT-ORIGINS.json',origins);save(L/'ROOT-PREP.json',dict(utc=now,lane=str(L),mathdb_id=338806,model='gpt-6.1-sol',reasoning='high',service='default',scientific_hold=True,credit=0,accepted_new=57,children=False,network=False,root_math_or_Lean_execution=False,protected_peers=['expanded-corpus-r513','expanded-corpus-r514']))
ff=[q for q in L.rglob('*') if q.is_file()];save(L/'frozen-inputs.json',{str(q):sha(q) for q in ff})
ready=dict(utc=now,lane=str(L),mathdb_id=338806,task_sha256=sha(L/'TASK.txt'),frozen_bindings=len(ff),model='gpt-6.1-sol',reasoning='high',service='default',credit=0,accepted_new=57,scientific_hold=True,protected_peers=['expanded-corpus-r513','expanded-corpus-r514'])
save(ROOT/'high-girth-ur-matching-formal-r4-ready.json',ready);save(ROOT/'selection-routing-high-girth-ur-matching-formal-r4.json',dict(ids=[338806],sources=['https://arxiv.org/abs/1803.11032'],lane=str(L),task_sha256=ready['task_sha256'],metadata_only=True))

base=read(ROOT/'r512-config.json');base.update(number=513,protected_peers=[L.name,'expanded-corpus-r514'],completed_discovery_numbers=sorted(set(base['completed_discovery_numbers'])|{512}),peer_routing_files=['selection-routing-high-girth-ur-matching-formal-r4.json'],denials=str(ROOT/'inherited-denials-r526.json'))
for name in ['high-girth-ur-matching-formal-parent-integration-r3.json','expanded-corpus-r512-parent-integration.json','product-measure-dimension-primary-parent-integration-r2.json']:base['steering']+='\n'+read(P/name)['scientific_summary']
base['steering']+='\nROOTcontinuesUNCREDITED338806formalresearchr4,NOTscientificPASS/acceptance/sourcewaiver;sealedfourmodulessource+oleanbaselinecopiedonlybyroottoownnewlane,allformalbodies/flatmetadataPROTECTEDtodiscovery. Product364140SCIENTIFICPARKafteractual2016boundednonmatchandunread403closedSuck2002/Jurdjevic-Sussmann1972proofs;allNEWdeliveriesofthoseidentifiedworksforbiddenincludingquery/METADATA/hosts/versions/cache/mirror/DOI/API/indirectrecovery. Otherdistinctpapersnotblanketdenied. Sourceheader2407PDFv2March2026correctionretained.57/60unchanged.\n'
save(ROOT/'r513-config.json',base);constructor=Path(base['metadata_constructor']);assert sha(constructor)=='37d7074c7f226a4f4940ce2b5a59c57e2b1a39ffdc339f1917cab5e68549c76b';assert sha(Path(base['metadata_selector']))=='677992b5a6b1b17e45afbb3ae30f11548a37531593082819165278ee7d65ebed'
spec=importlib.util.spec_from_file_location('discovery_soft',constructor);module=importlib.util.module_from_spec(spec);spec.loader.exec_module(module);r513=module.prepare(base)
nextbase=dict(base);nextbase.update(number=514,protected_peers=[L.name,'expanded-corpus-r513'],peer_routing_files=['selection-routing-high-girth-ur-matching-formal-r4.json','selection-routing-r513.json']);save(ROOT/'r514-config.json',nextbase);r514=module.prepare(nextbase)
for packet in [r513,r514]:
 for name in read(Path(packet['lane'])/'historical-results-allowlist.json'):
  rel=Path(name).relative_to(P);assert not any(t in part.lower() for part in rel.parts for t in ['formal','code-loop','code_loop','polynexus','crown','bunkbed','tournament','hat-bipartite'])
  assert not any(part in packet['active_peers'] or part in {f'expanded-corpus-r{x}' for x in [395,463,466,482]}|{f'expanded-corpus-r{x}-parent-integration.json' for x in [395,463,466,482]} for part in rel.parts)
save(ROOT/'formal-r3-r512-product-r2-next-routing.json',dict(utc=now,formal=ready,discovery=[r513,r514],credit=0,accepted_new=57,no_root_mathematics=True))
print(json.dumps(dict(formal=ready,discovery=[r513,r514],credit=0,accepted_new=57)))
