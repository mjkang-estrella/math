"""Root documentary integrity and clean target review; no mathematical execution."""
import os,resource
os.sched_setaffinity(0,sorted(os.sched_getaffinity(0))[:2]);resource.setrlimit(resource.RLIMIT_CPU,(120,120));resource.setrlimit(resource.RLIMIT_AS,(6*1024**3,6*1024**3))
from pathlib import Path
import json,hashlib,datetime,collections,re,shutil
P=Path(__file__).resolve().parent.parent;ROOT=P/'root-intake-r60';A=P/'expanded-corpus-r488';R=P/'saturated-avoidable-parity-source-review-sol-r1'
def sha(q):return hashlib.sha256(q.read_bytes()).hexdigest()
def dg(b):return hashlib.sha256(b).hexdigest()
def read(q):return json.loads(q.read_text())
def save(q,d):
 assert not q.exists(),str(q)
 q.write_text(json.dumps(d,indent=2)+'\n')
now=datetime.datetime.now(datetime.timezone.utc).isoformat();assert read(P/'ledger.json')['accepted_new']==57
route=read(ROOT/'selection-routing-r488.json');assert sha(A/'TASK.txt')==route['task_sha256'] and sha(A/'reservation.json')==route['reservation_sha256']
m=read(A/'MANIFEST.json');entries={v['path']:v for v in m['entries']};assert len(entries)==len(m['entries'])==165
for n,v in entries.items():
 assert not Path(n).is_absolute() and '..' not in Path(n).parts
 q=A/n;assert not q.is_symlink() and sha(q)==v['sha256'] and q.stat().st_size==v['bytes'],n
ex=m['terminal_noncircular_self_exclusions'];assert set(ex)=={'MANIFEST.json','terminal_manifest.receipt.json','terminal_manifest.output.txt'}
actual=set()
for q in A.rglob('*'):
 assert not q.is_symlink()
 if q.is_file():actual.add(str(q.relative_to(A)))
assert actual==set(entries)|set(ex)
frozen=read(A/'frozen-inputs.json');assert len(frozen)==13 and all(Path(n).parent==A and sha(Path(n))==h for n,h in frozen.items())
after=read(A/'frozen-after.json');before=read(A/'frozen-before.json');assert before['count']==after['count']==13 and before['mismatches']==after['mismatches']==[]
gates=read(A/'results.json');prov=read(A/'literal-bindings.json');ids=read(A/'reservation.json')['ids'];assert len(ids)==20 and set(ids)==set(map(int,gates))==set(map(int,prov))
chunks={};sources={}
for key,row in prov.items():
 q=Path(row['chunk']);assert q.is_relative_to(P.parent/'lanes/pi-mathdb-full-corpus-inventory-r301/corpus')
 if str(q) not in chunks:
  b=q.read_bytes();chunks[str(q)]=(dg(b),b.splitlines(keepends=True))
 h,lines=chunks[str(q)];assert h==row['chunk_sha256'];raw=lines[row['line']-1];obj=json.loads(raw)
 assert row['newline'] is True and raw.endswith(b'\n') and dg(raw)==row['raw_sha256'] and (A/'originals'/f'{key}.jsonl').read_bytes()==raw and obj==row['object'] and obj['mathdb_id']==int(key)
 tokens=re.findall(rb'"statement"\s*:\s*("(?:[^"\\]|\\.)*")',raw);assert len(tokens)==1;token=tokens[0]
 assert token.decode()==row['statement_token'] and dg(token)==row['statement_token_sha256'] and json.loads(token)==obj['statement'] and dg(obj['statement'].encode())==row['decoded_statement_sha256'];sources[key]=obj['source_url']
receipts=[]
for q in sorted(A.glob('*.receipt.json')):
 v=read(q);assert v['cwd']==str(A) and v['cpu_limit_s']==115 and v['as_limit_bytes']==6*1024**3 and v['deadline_s']==130 and len(v['affinity'])<=2 and v['group_rss_guard_bytes']==6*1024**3 and v['killed'] is None
 receipts.append(dict(path=q.name,sha256=sha(q),exit=v['exit']))
assert read(A/'terminal_manifest.receipt.json')['exit']==0 and read(A/'final_ocr.receipt.json')['exit']==1
budget=read(A/'search-budget.json');assert budget==dict(calls_used=3,queries_used=9,maximum_calls=3,maximum_queries=9,charged_before_call=True)
charges=[json.loads(s) for s in (A/'search-charges.jsonl').read_text().splitlines()];assert len(charges)==3
prev=dict(calls_used=0,queries_used=0,maximum_calls=3,maximum_queries=9,charged_before_call=True)
for word,c in zip(['one','two','three'],charges):
 assert c['sequence']==prev['calls_used']+1 and c['before']==prev and sha(A/c['plan'])==c['plan_sha256'] and read(A/c['plan'])['queries']==c['queries']
 nxt=dict(prev,calls_used=prev['calls_used']+1,queries_used=prev['queries_used']+len(c['queries']));assert c['after']==nxt;prev=nxt
 response=read(A/f'search-{word}-response.json');assert isinstance(response,str) and len(response)>1000
assert prev==budget and sha(A/'charge_search.py')==sha(ROOT/'charge_search.py')
events=[];prev='0'*64;pdfs=0
plans={dg(json.dumps(read(q),sort_keys=True).encode()):read(q) for q in (A/'plans').glob('*.json') if 'url' in read(q)}
for i,line in enumerate((A/'guard-ledger.jsonl').read_bytes().splitlines(keepends=True)):
 e=json.loads(line);assert e['seq']==i and e['previous']==prev;prev=dg(line);events.append(e)
 if e['event']=='success':
  q=A/e['destination'];assert sha(q)==e['sha256'] and q.stat().st_size==e['bytes']
  if q.read_bytes().startswith(b'%PDF'):pdfs+=1
 if e['event']=='attempt':assert e['plan_sha256'] in plans and '/server/api/' not in e['url'] and e['url'].startswith('https://') and set(e['routes'])<=set(map(str,ids))
counts=collections.Counter(e['event'] for e in events);assert counts==dict(attempt=10,success=10) and pdfs==6
history=read(A/'history-access.json');allow=read(A/'historical-results-allowlist.json');assert len(history)==813
forbidden=('formal','code-loop','code_loop','polynexus','crown','bunkbed','tournament','hat-bipartite')
for x in history:
 rel=Path(x['path']).relative_to(P)
 assert not any(t in part.lower() for part in rel.parts for t in forbidden)
 assert not any(f'expanded-corpus-r{n}' in x['path'] for n in [395,463,466,482]) and x['path'] in allow and allow[x['path']]==x['sha256']
summary='377665authorfullordinarynecessityproof arbitraryfinitelygeneratedabelianG/infiniteU viaoddreflectionobstruction/F2functionalextension/maximality/paritycoordinates. ActualfinalArsCombinatoria65(2002)pp279/280/286/287visuallyread,cachedsourceConj1matchesnecessity,separatesufficiencyexponent2exceptionnotcredited. ActualLiaoLiuZhangFilomat39:30(2025)Th2.4finitegroupoddproductproofread,authorproof-levelinfiniteextensionandcompleteparitymaximalitytargetbridge supportsROUTINEADAPTATIONproposal;independentproof/fidelity/significanceunpaid,assignedreview,nofinalexclusionyet.378080firstprefix/trace/shiftedpaircasepaid,arbitraryfamilyintermediateprefixmajorizationunpaid.377247regularplanarbipartitepubliccasepaid,irregularquadrangulationtestvector/discharging/inductionunpaid,specific2026Kolokolnikov/2013priorbodiesunreadHOLD.346828/377653actual2006.05511publicnonwellcoveredindependence-equivalenttreefamily0,figure/basecertificateandprintedrecurrencetyposnotindependentlycertified.'
record=dict(utc=now,source_lane=str(A),task_reservation_genesis_verified=True,manifest_sha256=sha(A/'MANIFEST.json'),verified_manifest_files=165,verified_original_bindings=sorted(ids),verified_frozen_bindings=13,source_url_by_id=sources,all20_gates=gates,runner_receipts=receipts,receipt_exit_counts=dict(collections.Counter(str(x['exit']) for x in receipts)),guard_events=dict(counts),search_budget=budget,root_disposition='ZERO_QUALIFIED_SURVIVORS_377665_ASSIGNED_INDEPENDENT_REVIEW',scientific_summary=summary,reading_limits='Fourassignedoriginalbodiesselected,sixteenunread. Actual2002finaltargetpassagesvisuallyread,notwholefinalproofaudit.2025finitepriorfullapplicableproofreadbyauthor,extensionnotindependentlyreviewed. Publictreefigures/baseanddeepdependenciesattributed.',process='165ownfiles20raw/token/decodedbindings13frozen813savedhistorynamesverifiedwithoutrootfollowingexternalpaths.10GETsuccess(6PDF4HTML),0redirect/denial,3chargedsearch9queries/fullresponsescontinuityverified. MissingtesseractOCRexit1retained;ownsavedPDFvisualrecovery,nodedependencyinstall/unchangedrerun. No freshrootmetadatareconstruction. Sampledtelemetry/native/transient/writerlimitsretained,nouniversalcomplianceclaim.',root_scope='Documentaryprovenance/integrity/routingonly,no root mathematical solving/programs/Lean/checkers.',credit=0,accepted_new=57,target_new=60,formal_dispatch=False,terminal_self_exclusions=ex)
delta='Completedr488zeroqualifiedsurvivors. '+summary+'165ownfiles20bindings13frozen813savedhistorypathsverified,10GETsuccess3search9queries,nonewdenials. MissingOCRtoolnonpassretained/visualrecovery,57/60unchanged.'
den=read(ROOT/'inherited-denials-r495.json');den['utc']=now;den['root_r488_scope']=delta;denpath=ROOT/'inherited-denials-r496.json'
# All integrity checks precede root-only integration and clean target review construction.
save(P/'expanded-corpus-r488-parent-integration.json',record);save(denpath,den)
assert not R.exists();R.mkdir();(R/'inputs').mkdir();base=P/'expanded-corpus-r433'
for name in ['bootstrap.py','run.py','write_lane.py','verify_frozen.py','registry-roots.json','source_get_guard.py','model-policy-sol-only.json']:shutil.copyfile(base/name,R/name)
shutil.copyfile(ROOT/'charge_search.py',R/'charge_search.py');shutil.copyfile(denpath,R/'inherited-denials.json')
literal=prov['377665']['object'];shutil.copyfile(A/'originals/377665.jsonl',R/'inputs/original377665.raw.jsonl');save(R/'inputs/provenance377665.json',prov['377665']);save(R/'inputs/literal377665.json',literal);save(R/'inputs/author-gates377665.json',gates['377665'])
for name in ['FULLCANDIDATE.md','DORMANT-SOL-FORMAL-PLAN.md']:shutil.copyfile(A/name,R/'inputs'/name)
for name in ['saturated.pdf','saturated.txt','saturated-final.pdf','saturated-final.txt','saturated-metadata.html','cayley-prior.pdf','cayley-prior.txt']:shutil.copyfile(A/'sources'/name,R/'inputs'/name)
for name in ['get-saturated.json','get-final-saturated.json','get-cayley-prior.json']:shutil.copyfile(A/'plans'/name,R/'inputs'/name)
shutil.copyfile(ROOT/'accepted57-review-context.json',R/'inputs/accepted57-scopes.json');prior=P/'spherical-error-monotonicity-source-review-sol-r1/inputs/prior39-routing.json';assert sha(prior)=='6493e29137d286242b09d96f97dfe39a9ca5146a8d73bcfa8177e4705d6aaff3';shutil.copyfile(prior,R/'inputs/prior39-scopes.json')
save(R/'reservation.json',dict(ids=[377665],rows=[literal],purpose='Independentfullsaturatedavoidableparitynecessityproofandfiniteprior-proof-extension/significancereview,noformaltools/selfacceptance'));(R/'reservation.sha256').write_text(sha(R/'reservation.json')+'  reservation.json\n');save(R/'search-budget.json',dict(calls_used=0,queries_used=0,maximum_calls=2,maximum_queries=6,charged_before_call=True))
task=f'''Use ONLY GPT-6.1 Sol, high effort, default speed. Personally and independently review MathDB377665's full necessity classification of saturated avoidable sets with no even elements, actual source/final semantics, infinite-group proof and complete public-proof adaptation/significance. Current57/60 beyond39prior,96total. No children/fallback/mathematicalprograms/formaltools/selfcredit. Rootorchestrates,youdo mathematics. Completeboundedreview,notacknowledgment/acquisitiononly.

FIRST shellcommand EXACTLY:
timeout 20 python3 -I -B {R}/bootstrap.py
Read COMPLETE printedTASK/AGENTS. SECOND EXACTLY:
timeout 140 python3 -I -B {R}/verify_frozen.py before
No punctuation/chaining. Bootstrap/standaloneverifiers explicitcapexceptions. Everyothersubstantivelocaloperation immutableABSOLUTE {R}/run.py UNIQUE_LABEL Pythonstdin; authoredwrites immutableABSOLUTE {R}/write_lane.py. Neverrerunbootstrap/editfrozenhelpers/inputs/TASK/caps. Preservefailures/targetedrepairsfreshlabels. Actualprotected/frozen/access/guard/counter/capbreach STOP/quarantine/noreset. Ordinarydocumentarytypo/render/serializationfailurenotautomaticallypolicybreach.

SOLE377665. Protectedactivepeers expanded-corpus-r489 and cubical-zigzag-source-review-sol-r1,evenmetadata/stat/read/hash/list/glob/poll/reservations/flatbasenames. NOhistoryallowlist. Ownfrozeninputs/products andexplicitPDFskillonly;noauthorlane/ROOT/campaign/history/embeddedpaths. Allformal/code-loop/Polynexus/crown/bunkbed/tournament/HatbodiesANDflatintegrationsprotected. ALLr395/r463/r466/r482packetspermanentlyquarantined,noreuse/refetchseeds. Public/server/api/.../contentforbiddenAPIevenPDF-looking/guard200. Allwritesownlane,no/tmp/shared/parent/git/install/publish/accounts/messages. Trusted57+39scopesboundedcontextonly,nocertificateaudit.

Readexactraw/literal and actual Develin math0211184v1 definitions,Section2.3Conj1 and precedingcontext,PLUSactualpublisherfinalArsCombinatoria65(2002)279-297 supplied. DetermineexactstandingfinitelygeneratedabelianG/decomposition/rank/torsion scope,avoidabilitypartitionandDISTINCTsummands,even=2G,saturated=maximalamongALLavoidablesets(notjustoddones),necessityversusconverse. Do notreplace conjecturewithstatementforfiniteG/finiteU orhomogeneouscoloring;do notclaimconverseifsourcehypothesesfail. CorpusUnderdiscussioncontextmustberecoveredwithzerocorrectioncredit. Allrangesincludingtrivialgroup/G=2G/zero-dimensionalparityquotient/Uempty/exponent2 checked,ratherthansilentlydropped.

Use/announce/read explicitPDFskill /home/mj-kang/.codex/plugins/cache/openai-primary-runtime/pdf/26.1103.10131/skills/pdf/SKILL.md; personallyvisuallyinspectmaterialfinaldefinitions/conjecture/formulaglyphs andrelevantpriorproof,notauthorreportalone. OriginalworkerOCRfailedmissing tesseract; doNOTinstallorretryunchangedOCR,renderexistingPDFandviewrelevantpages. FinalPDFtextmaycontainpage-extractionlimits,useactualrender. NoPDFauthoring. Sourceprecedingsufficiencymaybehasexponent2counterexample;keepitSEPARATEfromliteralnecessity,nohelper/domaincorrectioncredit/noentire-conjecturefailurefromconversealone.

IndependentlyconstructYOURfullordinaryproofbeforetrustingFULLCANDIDATE.md,thenadversariallyauditit. Authorroute:anavoiding2coloring makes eachreflectionR_u(x)=u-x togglecolor forEVERYx sinceu notin2G forbidsfixedpoints. AnoddlistofUwhoseparityimages sum0 yieldsalternatingAin2G; choose2x=A,oddreflectioncompositionfixesx,contradiction. Checkactualorder/signs,distinctsummandsateachstep,repeatedlabels/vertices/infinitelymanyU,non-simpleclosedwalk,2torsion. Thenallfiniteparityrelationsareeven,definefunctionalontheF2span(qU),provewell-definedlinearandextensiontoG/2G withoutunprovedambientfiniteness; sourcefinitelygeneratedensuresfiniteparitydimension. H=phi^-1(1)isavoidableandcontainsU;maximalityforcesU=H. PaynonemptyU/nonzerophi:authorusesavoidabilityof{{0}} viaoppositenegationpairswithsingletonorbitsallowedbecauseDISTINCTsummands. Sourcepartitionconventions/trivialcasecouldmatter;repairorpreciseGAP,notunprovedchoiceassertion. Paycoordinateformulaonfree/even/oddcyclicfactorsandallzero/zero-rankcases. Do notproveonlysubsetofhyperplaneorfinite-generationofU.

Actual2025Liao-Liu-Zhang On structural properties of generalized Cayley graphs Filomat39:30 10871-10882 DOI10.2298/FIL2530871L is supplied. Personallyreaddefinitions,Lemmas2.2/2.3,fullTheorem2.4proof/hypotheses. AuthorproposesfiniteGROUPtheorem'sPROOFextends toinfinitegroups/infiniteU withfinite-supportrelations,thenparitylinearalgebra/maximalitypaystarget. Afinite theoremstatementisNOTautomaticallyanall-finitely-generatedtheorem: mapalpha=inversion,adjacencyalpha(x^-1)y=x+y,omegaalpha=2G,conditionUdisjoint2G,undirected/simpleloopconventions,identityautomorphismcaseexponent2. Locateeveryuseoffiniteness/connectedness/shortestwalk/preimage/generatorassumptionintheactualproof. Ifextensionvalid,proveitexplicitly;nofalsecompactness/limittransfer. Ifnewnontrivialinfinitebridgeunpaid,identifyandproveorprecisegap. Actual2003Cheyne-Gupta-Wheelerbipartitenesscriteria referenceisaleadwithunreadbody,notanauthenticatedall-Gsolution;boundedprimarycomparisononlyifneededforconcretetheorem-levelassessment.

Scientificgate:strongpositivecase sourceexplicitConj1andfullpotentiallyinfiniteG/U classificationrequiresmorethanfinitepriorstatement,plusmaximality/paritycoordinates. Strongcontrarycase actual2025odd-productproofextendsverbatimwithoutambientcardinalityandtargetthenfollowsbyelementaryF2functional/maximality,completepublic-proofroutineadaptation. Judgeactualcompletebridge,notshortness/standardtools/openlabel. Ifexclude,giveeveryprior-to-targethypothesis/extensionstepandstrongopposingcase,notclaimearlierexactprintedDevelinsolutionwithoutactualbody. Ifsubstantive,preciselywhynewextensionismorethanroutineandwhatactualpriorfailscover. No genericworldwide-unknownveto,boundednonmatchesnotnovelty;specificmatchingunreadproofispreciseHOLD. Sourcefinalfidelityalreadyhasactualcachedfinalbody;do notfalselyretainunavailablefinalgatewithoutreadingit.

Compareall57+39suppliedexactscopesonly. Otherfinitegroups/parity/code-loop/matchingcoset resultsnotduplicatesbyvocabulary; alleven-free/saturated/paritycoordinate/parameter/finiteinfinitevariantsonefamily. Source/domain/converse/endpointcorrections,helpers,formalization,public/routineoutcomeszero. Nomathematicalprograms/enumeration/numericaltests/CAS/solver/Lean/compiler/checker/formalAPI. Personalordinaryreasoningonly;documentary/hash/source/PDFprocessingallowed. ConditionaldormantSolbriefonlyiffullordinaryliteral/scientificgatessurvive,withactualavoidability/distinctsum/maximality/finitelygeneratedG/2G/F2hom/classificationliteralbridges;noimplementation/dispatch/selfacceptance.

NetworkreadENTIREinherited-denials/recovermaterialtruncationsBEFORErequests. Cachedactualoriginal/final/2025priorprovided; do notwasteGETreacquiring. SoleGETimmutable source_get_guard.py UNDERrun.py,ONEmanuallyselectedexactpersistedplan/invocation,url/routes/destination/source_identity/purpose,route['377665'],NEWownsourcesdestination,identity/purpose>=12chars. Max6GETHOPSincludingredirects;max2nativeSEARCHcalls6exactquerystrings. BeforeEACHsearchpersistqueries-listplanviawriter,readLIVEcounter/ledger,prechargeimmutableABSOLUTEcharge_search.py underrunner,neverreset/refund/manualcounteredits. SaveFULLactualresponseimmediatelybeforeotherwork,ordinaryJSON/string,no btoa/TextEncoder;recoverSAMEinmemoryresponsewithoutanothercallonlocalserializationfailure. Searchnavigationnotproof.
NoAPIincludingpublic/server/api bitstreams,customHTTP/curl/wget/requests/HEAD/nativeopenfetch/browser/accounts/POST/TLS/cookie/JS/meta-refreshworkaround. EveryfailureidentifiedworkALLNEW hosts/versions/arxiv/authors/caches/mirrors/DOI/API/body/metadata deliveriesunavailable,noretry/identitycorrection/indirectrecovery. Allinheritedblocksapply,includingmath0608694original(failed503),tree2507.18272DOI10.1007/s00010-026-01266-w,math0601731polydigraph,0704.0541fixedunitsums,1106.5068EPS/2014Poly-antimatroidpolyhedra. Explicitcachedpredenialcopiesonlynotfinalequivalence;distinctotherpapersnotblanketdenied. Fourregistryrootmetadataartifactsunavailable,norefresh/reconstructionviaREADME/tree/API/branch/version. Guardhistoryunchanged;transport200nonpaperclassifiedseparately.

Capsaffinity<=2,childCPU115/supervisor120,AS6GiB,sampledgroupRSS6GiB,deadline130/outer140,arena2. Allsynchronousrunnerreceiptsactualresources/reaping,nobackgroundjobs. StandaloneverifierCPU120exceptionnotnestedunderchild115. Native/transient/writer/supervisorpeaksunknown,nouniversalcomplianceclaim.

DeliverREVIEW.md,independentPROOF.mdorpreciseGAP.md,keyedreview.json377665 separateliteral/source/ordinary/prior/novelty/significance/family/formal/independent/procedure/acceptancegates,source-map/strongestopposingcases,read/visual/access/search/resourceinventories,actualreceipts/hashmanifest. Finalstandalonefrozen-after THENmanifestEVERYownfile/helpers/frozeninputs/plans/payloads/fullresponses/ledgers/ALLcompletedreceiptJSON,preciselynamedterminalnoncircularexclusions,nolaterfrozenwrites. Completeboundedreviewordocumentprecisegaps. Credit0,57/60unchangeduntilrootacceptance.
'''
(R/'TASK.txt').write_text(task);files=[q for q in R.iterdir() if q.is_file() and q.name!='search-budget.json']+list((R/'inputs').iterdir());save(R/'frozen-inputs.json',{str(q):sha(q) for q in files})
ready=dict(utc=now,lane=str(R),mathdb_id=377665,task_sha256=sha(R/'TASK.txt'),frozen_bindings=len(files),model='gpt-6.1-sol',reasoning='high',service='default',accepted_new=57,credit=0,protected_peers=['expanded-corpus-r489','cubical-zigzag-source-review-sol-r1'],source_copy_scope='Cleanr488target-onlyliteral/provenance/authorproof/cachedactualoriginal+publisherfinal+2025prior/57+39scopes,noquarantine')
save(ROOT/'avoidable-parity-review-r1-ready.json',ready);save(ROOT/'selection-routing-avoidable-parity-review-r1.json',dict(ids=[377665],sources=[literal['source_url']],lane=str(R),task_sha256=ready['task_sha256'],metadata_only=True));save(ROOT/'r488-completion-boundary-delta.json',dict(utc=now,message=delta,new_protected_peer=R.name,immutable_worker_inputs_unchanged=True))
print(json.dumps(dict(manifest_files=165,frozen_bindings=13,original_bindings=20,receipt_exit_counts=record['receipt_exit_counts'],review=ready)))
