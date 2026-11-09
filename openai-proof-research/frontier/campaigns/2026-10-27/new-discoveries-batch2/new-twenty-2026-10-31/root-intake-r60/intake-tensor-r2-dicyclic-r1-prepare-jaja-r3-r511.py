"""Documentary intake, bounded qualification routing and disjoint metadata selection only."""
import os,resource
os.sched_setaffinity(0,sorted(os.sched_getaffinity(0))[:2])
resource.setrlimit(resource.RLIMIT_CPU,(120,120))
resource.setrlimit(resource.RLIMIT_AS,(6*1024**3,6*1024**3))
from pathlib import Path
import json,hashlib,datetime,re,collections,ast,shutil,importlib.util
ROOT=Path(__file__).resolve().parent;P=ROOT.parent;chunks={}
t=ast.parse((ROOT/'intake-planar-review-r506-prepare-r508-r509.py').read_text());exec(compile(ast.Module(body=[x for x in t.body if isinstance(x,ast.FunctionDef)],type_ignores=[]),'<documentary-functions>','exec'),globals())
now=datetime.datetime.now(datetime.timezone.utc).isoformat();assert read(P/'ledger.json')['accepted_new']==57
T=P/'tensor-dominant-orbit-primary-qualification-sol-r2';D=P/'dicyclic-mstd-fixed-size-source-review-sol-r1'
records={}
for mid,a,mname,count,fcount,readyfile,terminal in [(323694,T,'SHA256-MANIFEST.json',115,31,'tensor-dominant-orbit-qualification-r2-ready.json','terminal_seal'),(373070,D,'MANIFEST.json',107,33,'dicyclic-mstd-review-r1-ready.json','seal_manifest')]:
 ready=read(ROOT/readyfile);assert sha(a/'TASK.txt')==ready['task_sha256'];m=read(a/mname);assert len(m['files'])==count
 names=set()
 for x in m['files']:
  n=x['path'];assert not Path(n).is_absolute() and '..' not in Path(n).parts and n not in names;names.add(n)
  q=a/n;assert not q.is_symlink() and sha(q)==x['sha256'] and q.stat().st_size==x['bytes']
 ex=read(a/'TERMINAL-EXCLUSIONS.json')['excluded'] if mid==323694 else m['terminal_noncircular_exclusions']
 assert set(ex)=={mname,terminal+'.receipt.json',terminal+'.output.txt'}
 inventory=set()
 for q in a.rglob('*'):
  assert not q.is_symlink()
  if q.is_file():inventory.add(str(q.relative_to(a)))
 assert inventory==names|set(ex);frozen(a,fcount)
 fail={'get_sumi_journal.receipt.json':1} if mid==323694 else {'independent_proof_render.receipt.json':1,'scopes57_read.receipt.json':1}
 rec=receipts(a,fail);assert read(a/(terminal+'.receipt.json'))['exit']==0
 prov=read(a/'inputs'/f'provenance{mid}.json');raw,obj,token=corpus(prov)
 assert raw==(a/'inputs'/f'original{mid}.raw.jsonl').read_bytes() and obj==read(a/'inputs'/f'literal{mid}.json')==read(a/'reservation.json')['rows'][0] and obj['mathdb_id']==mid
 assert token.decode()==prov['statement_token'] and dg(token)==prov['statement_token_sha256'] and dg(obj['statement'].encode())==prov['statement_utf8_sha256']
 review=read(a/'review.json');assert review[str(mid)]['gates']['ordinary']
 if mid==323694:
  budget=search(a,2,6,2,6,['search1-fullresponse.json','search2-fullresponse.json'])
  events=guard(a,list(a.glob('get-*.json')),[mid],dict(attempt=4,success=3,unavailable=1),1)
  source=read(a/'source-map.json')[str(mid)]
  for n,h in source['source_hashes'].items():assert sha(a/n)==h
 else:
  assert read(a/'search-budget.json')==dict(calls_used=0,queries_used=0,maximum_calls=2,maximum_queries=6,charged_before_call=True)
  assert 'guard-ledger.jsonl' not in inventory and 'search-charges.jsonl' not in inventory
  sc=read(a/'scope-comparison96.json');rows=sc if isinstance(sc,list) else next(x for x in sc.values() if isinstance(x,list) and len(x)==96);assert len(rows)==96
  source=read(a/'source-map.json')
  for x in source[str(mid)]:
   if 'pdf' in x:
    q=Path(x['pdf']);assert q.is_relative_to(a) and sha(q)==x['sha256']
 records[mid]=dict(utc=now,mathdb_id=mid,source_lane=str(a),task_sha256=sha(a/'TASK.txt'),manifest_sha256=sha(a/mname),verified_manifest_files=count,verified_frozen_bindings=fcount,verified_original_bindings=[mid],review=review,source_map=source,runner_receipts=rec,credit=0,accepted_new=57,formal_dispatch=False,terminal_self_exclusions=ex,root_scope='Documentary integrity/routing/credit policy only; no root mathematical solving/programs/Lean/checkers.')
ts='323694 actualSumi0808.1167v3 primarytheorem/proofread withmaterialglyphs: wholesaleR/C3.6/3.8/Cor3.10 finitefieldnonmatch;3.3 genuinelyarbitraryKsmall-squarehelperpossibilitybutactualJaJa upperproofattributednotread. Prop3.4 actualF2 obstructiondifferent3x3x2format,notcounterexampletotarget; no completeall-pbinaryproductorbit/countpriorsubsumerbridgeauthenticated. Ordinaryfulltensorendpoint PASS retained;originalfreshofficialmetadataonlyv1/nojournal boundedcurrent-recordevidence,notabsencecertificate. SpecificJaJa1979actualobservedhttps://epubs.siam.org/doi/abs/10.1137/0208037 bodyunread;onefocusedcomparisonassigned,no newgeneralproofreplay. Sumi2009final403 closesENTIREidentifiedwork(allversions0808.1167/DOI10.1016/j.laa.2009.06.023/S002437950900319X),predeliveryv3notfinalequivalence. ROOT scientificHOLD,notpublic/routineexclusion;positiveexactall-p/hyperplanestructurecaseandcompleteconventionalnormalformobjectionretained.115manifestfiles31frozen1corpusbinding,4GET3payloads1PDF2HTML1HTTP403,2search6strings,21runnerreceiptsincludingfailed403 retained. Trustedprevious96scopenonmatch/notrepeated. Resource/truncation/readlimits retained,noformaldispatch/credit.'
ds='373070 independentfullordinary/cachedliteral PASS: allfixedm>=2/alllargenbothparities,explicitthreshold,2n distinctm-subsets,product/inverseproductcounts4m-4/4m-5,strictgrowthbound,group/cardinalitybridgespaid. Wholeavailable2022dihedralabundance/collisionproofread;involutiveflipfailsdicyclicb²shift,analogyisreviewerauthorednotauthenticatedearlierresolution. Specific2024quaternionconstruction/proofremainsUNREADandENTIREworkclosed;total-subsetsmetadata notfixedsize subsumption. ROOT SCIENTIFIC_PARK,notroutine/publicexclusion;sourcefinal/2026chapter/currentprior/significanceunpaid,noformaldispatch.107manifestfiles33frozen1corpusbinding96personalscopecomparisonsverified,0newGET/search,19runnerreceiptsincludingmissingfitz andscope-keyexit1bothhonestlyrepaired. Denialfullreadnotclaimed/no requesteligibilityexercised;inheritedSTOP/loggerfailure/dateerratumretained,unknownnative/transient/writerpeaks,no universalprocessclearance. Credit0/57unchanged.'
records[323694].update(scientific_summary=ts,root_disposition='ORDINARY_PASS_SCIENTIFIC_HOLD_JAJA_FOCUSED_REVIEW_ASSIGNED')
records[373070].update(scientific_summary=ds,verified_saved_scope_comparisons=96,root_disposition='SCIENTIFIC_PARK_SPECIFIC_CLOSED_PRIOR_CONSTRUCTION_UNPAID')
den=read(ROOT/'inherited-denials-r522.json');den['utc']=now;den['root_tensor323694_r2_scope']=ts;den['root_dicyclic373070_review_scope']=ds
stop=read(T/'NEW-UNAVAILABLE.json');failure=next(x for x in events if x['event']=='unavailable');assert failure['status']==403
den['blocked_keys']=sorted(set(den['blocked_keys'])|{failure['url_key'],'doi.org/10.1016/j.laa.2009.06.023','arxiv.org/abs/0808.1167','arxiv.org/pdf/0808.1167'})
den['blocked_artifacts']=sorted(set(den['blocked_artifacts'])|{'rank of 3-tensors with 2 slices and kronecker canonical forms','0808.1167','10.1016/j.laa.2009.06.023','s002437950900319x'})
den['records'].append(dict(url=failure['url'],reason=dict(status=403,artifact=stop['work'],restriction=stop['closure']+' DistinctJaJa1979worknotblanketdenied;noindirectSumiworkrecovery.'),evidence=dict(path=str(T/'NEW-UNAVAILABLE.json'),sha256=sha(T/'NEW-UNAVAILABLE.json'),guard_sha256=sha(T/'guard-ledger.jsonl'))))
# All documentary checks precede root mutations.
save(P/'tensor-dominant-orbit-primary-parent-integration-r2.json',records[323694]);save(P/'dicyclic-mstd-fixed-size-source-parent-integration-r1.json',records[373070]);denpath=ROOT/'inherited-denials-r523.json';save(denpath,den)
L=P/'tensor-dominant-orbit-jaja-primary-sol-r3';assert not L.exists();L.mkdir();(L/'inputs').mkdir()
for h in ['bootstrap.py','run.py','write_lane.py','verify_frozen.py','registry-roots.json','source_get_guard.py','model-policy-sol-only.json','charge_search.py']:shutil.copyfile(T/h,L/h)
shutil.copyfile(denpath,L/'inherited-denials.json')
for f in ['original323694.raw.jsonl','literal323694.json','provenance323694.json','tensor.pdf','tensor.txt','accepted57-scopes.json','prior39-scopes.json','prior-review-family-comparison96.json']:shutil.copyfile(T/'inputs'/f,L/'inputs'/f)
for f in ['REVIEW.md','PROOF.md','GAP.md','review.json','source-map.json','NEW-UNAVAILABLE.json','search1-fullresponse.json','search2-fullresponse.json']:shutil.copyfile(T/f,L/'inputs'/('r2-'+f))
shutil.copyfile(T/'sources/original-current.html',L/'inputs/original-current.html')
shutil.copyfile(T/'sources/sumi.pdf',L/'inputs/predelivery-sumi-v3.pdf');shutil.copyfile(T/'sources/sumi.txt',L/'inputs/predelivery-sumi-v3.txt')
literal=read(T/'inputs/literal323694.json');save(L/'reservation.json',dict(ids=[323694],rows=[literal],purpose='Last concrete JaJa primary-proof and bounded significance comparison, no formal tools'))
(L/'reservation.sha256').write_text(sha(L/'reservation.json')+'  reservation.json\n');save(L/'search-budget.json',dict(calls_used=0,queries_used=0,maximum_calls=2,maximum_queries=6,charged_before_call=True))
t=ast.parse((ROOT/'prepare-covariance-planar-reviews-r506.py').read_text());common=next(ast.literal_eval(x.value) for x in t.body if isinstance(x,ast.Assign) and any(isinstance(y,ast.Name) and y.id=='COMMON' for y in x.targets))
detail='''FOCUSED LAST CONCRETE323694 qualification: actualJaJa1979 primaryproof,notthirdgenericordinaryreplay. Trustsuppliedindependentordinary/source-v1PASS and96-scopeboundednonmatch; personallyinspectonlyneededcoreforcomparison. This overridesgenericrepeatfullreconstruction/96comparison. ReadCOMPLETEinheritedunioninboundedsegmentsbeforeanyrequest. NewSumiENTIREwork0808.1167/DOI10.1016/j.laa.2009.06.023/S002437950900319Xclosedafter403: no NEWbody/METADATA/query/versions/arxiv/authors/cache/mirror/DOI/API/indirectrecovery. OwnexplicitpredeliverySumiPDFisallowednotfinalequivalence. JaJa1979isDISTINCTearlierprimarywork,notalternateSumiworkdelivery.
Actualobservedprimaryroute fromr2source-map: https://epubs.siam.org/doi/abs/10.1137/0208037,JaJa Optimal evaluation ofpairs ofbilinear forms,SIAMJComput8(1979)443-462. NoJaJabodypreviouslyacquired/read/denied. Authenticateidentityfromactualsource/observedlinks,readapplicable theorem ANDproof; no guessedPDFURL, no alternateorHTTPSupgradeafterfailure. If403/redirectguardfailure closesJaJaSTOP,recordprecisebodygap,noretry/sourceproxies/indirectrecovery. Otherbodyroutesonlyifactuallyobservedbeforefailure andworknotclosed,notidentitycorrection.
ConcreteclaimreportedbyactuallyreadSumi v3Th3.3: arbitraryK,squarenxn A,k invariantpolynomialsnotfactoringintodistinctlinearfactors,CardK>=degp1(A),rank_K(I_n;A)<=n+k anddiagonalizabilityafteraddingkrankone terms; attributedupperboundproofJaJa. OtheractualJaJapencil/blockadditivitytheoremsmayberelevant. PayactualfiniteF2/binaryfield/cardinalityhypotheses,rectangular2-by-p pairsversussquareinvertible-first-slice,allowedproductGLp xGL2 xGL2,ordinarytensor-rank4uniquenessandframecount/allp limit. Do nottransfercomplex/real/largefieldtheorem. Do nottreatarbitrarymatrixcolumnoperationsastensorsymmetries. Ifactualearlierclassificationproofcompletelysubsumes,paytheFULLall-hypotheses-to-literalreductionand labelroutineapplication/exactearlierprintedsolutioncorrectly. Ifnotapplicable,concretetheorem-levelnonmatch. A helperaloneisnotfullpriorsolution; a completecurrentreductionaloneisnotearlierproofauthentication. Determinewhetherexistinghyperplanelemmaisadditionalstructuralcontentorfullyroutineapplicationwithactualprimaryproofandstrongestopposition,notshortness/familiarityalone.
Boundedversionpolicyclarification: officialcurrentarXiv1206.5179metadatafreshlyread2026-11-08 showsONLYv1/nojournal,twocurrentsearchesidentifyNOspecificfinal/correction. Thisisboundedcurrent-recordevidence,NOTcertificateofworldwideabsence. Do NOTdemandimpossibleabsenceofeverypublication/correction. IfaCONCRETEidentifiedfinal/correctioncounterclaimexists,itmustbechecked;otherwise reportboundedstatusratherthananautomaticgenericunknownveto. Thisdoesnotbyitselfestablishnovelty/significance. SpecificapplicableunreadJaJaproofremainsrealgapifnotresolved. No neworiginalmetadata/repeatedgenericsearchneededunlessactualnewcounterclaimarises.
Paidordinarymechanism: fourindependentfirst-modecolumns,singleorbitviaGLp alone,4simpletermsandflatteninglowerboundrank4. EverydeficientrowspaceinM2binaryhyperplane,dualcoefficientB^-t C D^-1 rank1or2normalformE11/I; explicitrankonebasesE12,E21,E22orE12,E21,J giverank<=3. Countproduct(2^p-1)(2^p-2)(2^p-4)(2^p-8),defect<=15*2^-p,allintegerp>=4. Originalsource2012explicitConj2,notConj1tenorbits. R2 personallyreadSumiR/Cproofsnonmatch,valid3.3smallbinarysquarehelpernotblanketexcluded,finitefield3x3x2obstructionNOTtargetcounterexample. No rerenderallSumi13pagesornewSumiqueries; usecopiedevidenceforhypothesisnavigationonly.
Strongpositive fullall-popenconjecture/uniqueactualrank4/hyperplane/exactcount;strongnegative completenormalform/frame/hyperplanereductionmayberoutineifactualprimaryproofcoversit. Give reasonedboundedprospectivequalification ORcompletepublic/routineexclusion ORpreciseGAP. No worldwidenoveltyclaim,noexclusionfromsnippet/abstract,notarbitrarynewpaperlist. Thisislastnamedprimarygap,notlicenseforinfinitegenericpriorhunt. OrdinaryproofalreadyPASS; noformaltools/selfcredit. ConditionaldormantfullliteralSolbriefONLYifscientificprospectivegatesclear; otherwiseparkprecisely. All4registryroots/aimathindex/otherinheritedworkclosuresremain,no source/root/certificateaccess.
'''
peers=['high-girth-ur-matching-primary-qualification-sol-r2','expanded-corpus-r511'];task=common.format(lane=L,id=323694,peers=', '.join(peers))+'\nTARGET-SPECIFIC FOCUSED JAJA REVIEW\n'+detail
(L/'TASK.txt').write_text(task);ff=[q for q in L.iterdir() if q.is_file() and q.name!='search-budget.json']+list((L/'inputs').iterdir());save(L/'frozen-inputs.json',{str(q):sha(q) for q in ff})
ready=dict(utc=now,lane=str(L),mathdb_id=323694,task_sha256=sha(L/'TASK.txt'),frozen_bindings=len(ff),model='gpt-6.1-sol',reasoning='high',service='default',accepted_new=57,credit=0,protected_peers=peers)
save(ROOT/'tensor-dominant-orbit-jaja-r3-ready.json',ready);save(ROOT/'selection-routing-tensor-dominant-orbit-jaja-r3.json',dict(ids=[323694],sources=[literal['source_url']],lane=str(L),task_sha256=ready['task_sha256'],metadata_only=True))
base=read(ROOT/'r510-config.json');base.update(number=511,protected_peers=['high-girth-ur-matching-primary-qualification-sol-r2',L.name],completed_discovery_numbers=sorted(set(base['completed_discovery_numbers'])|{509,510}),peer_routing_files=['selection-routing-high-girth-ur-matching-qualification-r2.json','selection-routing-tensor-dominant-orbit-jaja-r3.json'],denials=str(denpath))
base['excluded_ids']=sorted(set(base['excluded_ids'])|{373070,323694,338806});base['excluded_sources']=sorted(set(base['excluded_sources'])|{'https://arxiv.org/abs/2602.09073','https://arxiv.org/abs/2210.00669','https://arxiv.org/abs/1206.5179','https://arxiv.org/abs/0808.1167','https://arxiv.org/abs/1803.11032'})
base['steering']+='\n'+ts+'\n'+ds+'\nNEW ENTIRE Sumi-Miyazaki-Sakata Rank of3-tensors with2slices andKronecker canonicalforms,0808.1167/DOI10.1016/j.laa.2009.06.023/S002437950900319X closedafterHTTP403;ALLNEWbody/METADATA/query/host/version/arxiv/author/cache/mirror/DOI/API/indirectdeliveries forbidden. DistinctJaJa1979notblanketdenied. Dicyclic373070 SCIENTIFIC_PARKspecificclosed2024priorbodyunpaid,noreuseasqualified. Rootstill57/60,96total.\n'
save(ROOT/'r511-config.json',base);constructor=Path(base['metadata_constructor']);assert sha(constructor)=='37d7074c7f226a4f4940ce2b5a59c57e2b1a39ffdc339f1917cab5e68549c76b';assert sha(Path(base['metadata_selector']))=='677992b5a6b1b17e45afbb3ae30f11548a37531593082819165278ee7d65ebed'
spec=importlib.util.spec_from_file_location('discovery_soft',constructor);module=importlib.util.module_from_spec(spec);spec.loader.exec_module(module);new=module.prepare(base)
for name in read(Path(new['lane'])/'historical-results-allowlist.json'):
 rel=Path(name).relative_to(P);assert not any(t in part.lower() for part in rel.parts for t in ['formal','code-loop','code_loop','polynexus','crown','bunkbed','tournament','hat-bipartite'])
 assert not any(part in base['protected_peers'] or part in {f'expanded-corpus-r{x}' for x in [395,463,466,482]}|{f'expanded-corpus-r{x}-parent-integration.json' for x in [395,463,466,482]} for part in rel.parts)
save(ROOT/'tensor-r2-dicyclic-r1-completion-boundary-delta.json',dict(utc=now,message=ts+'\n'+ds,new_protected_peers=[L.name,'expanded-corpus-r511'],immutable_worker_inputs_unchanged=True,credit=0,accepted_new=57))
print(json.dumps(dict(files={k:v['verified_manifest_files'] for k,v in records.items()},frozen=64,corpus_bindings=2,review=ready,discovery=new,credit=0,accepted_new=57)))
