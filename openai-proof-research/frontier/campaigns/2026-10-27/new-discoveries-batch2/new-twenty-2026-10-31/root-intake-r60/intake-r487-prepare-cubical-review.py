"""Root documentary verification and clean target-only review preparation; no mathematics."""
import os,resource
os.sched_setaffinity(0,sorted(os.sched_getaffinity(0))[:2]);resource.setrlimit(resource.RLIMIT_CPU,(120,120));resource.setrlimit(resource.RLIMIT_AS,(6*1024**3,6*1024**3))
from pathlib import Path
import json,hashlib,datetime,collections,re,base64,shutil
P=Path(__file__).resolve().parent.parent;ROOT=P/'root-intake-r60';A=P/'expanded-corpus-r487';R=P/'cubical-zigzag-source-review-sol-r1'
def sha(q):return hashlib.sha256(q.read_bytes()).hexdigest()
def dg(b):return hashlib.sha256(b).hexdigest()
def read(q):return json.loads(q.read_text())
def save(q,d):
 assert not q.exists(),str(q)
 q.write_text(json.dumps(d,indent=2)+'\n')
now=datetime.datetime.now(datetime.timezone.utc).isoformat();assert read(P/'ledger.json')['accepted_new']==57
route=read(ROOT/'selection-routing-r487.json');assert sha(A/'TASK.txt')==route['task_sha256'] and sha(A/'reservation.json')==route['reservation_sha256']
m=read(A/'SHA256-MANIFEST.json');entries=m['files'];assert isinstance(entries,dict) and len(entries)==120
for n,v in entries.items():
 assert not Path(n).is_absolute() and '..' not in Path(n).parts
 q=A/n;assert not q.is_symlink() and sha(q)==v['sha256'] and q.stat().st_size==v['bytes'],n
ex=m['terminal_noncircular_self_exclusions'];assert set(ex)=={'SHA256-MANIFEST.json','final-manifest.receipt.json','final-manifest.output.txt'}
actual=set()
for q in A.rglob('*'):
 assert not q.is_symlink()
 if q.is_file():actual.add(str(q.relative_to(A)))
assert actual==set(entries)|set(ex)
frozen=read(A/'frozen-inputs.json');assert len(frozen)==13 and all(Path(n).parent==A and sha(Path(n))==h for n,h in frozen.items())
after=read(A/'frozen-after.json');before=read(A/'frozen-before.json');assert before['count']==after['count']==13 and before['mismatches']==after['mismatches']==[]
gates=read(A/'results.json');prov=read(A/'original-bindings.json');ids=read(A/'reservation.json')['ids'];assert len(ids)==20 and set(ids)==set(map(int,gates))==set(map(int,prov))
chunks={};sources={}
for key,row in prov.items():
 q=Path(row['chunk']);assert q.is_relative_to(P.parent/'lanes/pi-mathdb-full-corpus-inventory-r301/corpus')
 if str(q) not in chunks:
  b=q.read_bytes();chunks[str(q)]=(dg(b),b.splitlines(keepends=True))
 h,lines=chunks[str(q)];assert h==row['chunk_sha256'];raw=lines[row['line']-1];obj=json.loads(raw)
 assert row['newline'] is True and raw.endswith(b'\n') and dg(raw)==row['raw_sha256'] and base64.b64decode(row['raw_base64'],validate=True)==raw and obj==row['object'] and obj['mathdb_id']==int(key)
 tokens=re.findall(rb'"statement"\s*:\s*("(?:[^"\\]|\\.)*")',raw);assert len(tokens)==1;token=tokens[0]
 assert token.decode()==row['statement_token'] and dg(token)==row['token_sha256'] and json.loads(token)==row['statement']==obj['statement']==gates[key]['literal'] and dg(obj['statement'].encode())==row['statement_sha256'];sources[key]=obj['source_url']
receipts=[]
for q in sorted(A.glob('*.receipt.json')):
 v=read(q);assert v['cwd']==str(A) and v['cpu_limit_s']==115 and v['as_limit_bytes']==6*1024**3 and v['deadline_s']==130 and len(v['affinity'])<=2 and v['group_rss_guard_bytes']==6*1024**3 and v['killed'] is None
 receipts.append(dict(path=q.name,sha256=sha(q),exit=v['exit']))
assert read(A/'final-manifest.receipt.json')['exit']==0 and read(A/'get-tree-final.receipt.json')['exit']==1
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
counts=collections.Counter(e['event'] for e in events);assert counts==dict(attempt=9,success=6,redirect=3,unavailable=1) and pdfs==5
assert events[-1]['event']=='unavailable' and 'Already attempted URL' in events[-1]['error'] and events[-1]['url_key']=='link.springer.com/article/10.1007/s00010-026-01266-w'
history=read(A/'history-access.json');allow=read(A/'historical-results-allowlist.json');assert len(history)==809
forbidden=('formal','code-loop','code_loop','polynexus','crown','bunkbed','tournament','hat-bipartite')
for x in history:
 rel=Path(x['path']).relative_to(P)
 assert not any(t in part.lower() for part in rel.parts for t in forbidden)
 assert not any(f'expanded-corpus-r{n}' in x['path'] for n in [395,463,466,482]) and x['path'] in allow and allow[x['path']]==x['sha256']
summary='378413authorfullproposedfinitecubical3-complexquotientcounterexampleuses100translations/glide(11-x,y+10,z+10),localdisplacement10/thinintervalproof,flagT3translation/T30sigma1identity. Source/prior/orientability-significance/independentreviewunpaid; assignedcleantargetreview,noformaldispatch/PASS.341022actualhostdisplayedAug17,2026publicfixed-orderneuralcodecounterexamplecheckedincludinginhomogeneousdegree<=2fiberdivisors,public0,notmachinejudgelabel/independentarchivaldateclaim.377989actualOrdenetal0307370v3Theorem1givenplaneembeddingequivalencepublic0,deepgluing/Tutteinputsnotindependentlyaudited.375723literalreportssourcesolvesit,bodyunread,0.369466arbitrary-pboundarycompatiblelocalrepair/disjointd-pathchargingunpaid;378415exactflagreturnperiodandorientation-sensitiveorbitintersectionclassificationunpaid,totalflagcountinsufficient.'
record=dict(utc=now,source_lane=str(A),task_reservation_genesis_verified=True,manifest_sha256=sha(A/'SHA256-MANIFEST.json'),verified_manifest_files=120,verified_original_bindings=sorted(ids),verified_frozen_bindings=13,source_url_by_id=sources,all20_gates=gates,runner_receipts=receipts,receipt_exit_counts=dict(collections.Counter(str(x['exit']) for x in receipts)),guard_events=dict(counts),search_budget=budget,root_disposition='ZERO_QUALIFIED_SURVIVORS_PRESTOP_378413_ASSIGNED_INDEPENDENT_REVIEW',scientific_summary=summary,reading_limits='Fourassignedoriginalbodiesread,sixteenunread;actual1509.03754v3pp1-9selectedpassagesboundednonmatch,rest/final/laterlengthspaperunpaid. Cached0405279v1p5visualonly,notallglyphaudit. No independentordinary/scientificPASS.',process='RootretainsguardSTOP/nonPASS/quarantinenoticeandfailedreceipt.9chargedGET6payloads(5PDF1publicHTML),3redirects,oneunavailable. AutomaticSpringercookieauthorize/transitrequestsperformedandrecorded,butguardpreventedrepeatarticlefetchbeforedispatch;no manualretry/cookieworkaround/guardedit/counterreset/protectedread/APIacquisitionestablished. No fabricatedcleanuniversalPASSorperformedrepeat. Pre-stopmathematicalevidenceretainedunacceptedforfreshindependentreview;blockedtreeworknonewdelivery.120ownfiles20bindings13frozen809savedhistorynamesverified,3search9queries/fullresponses. No rootfollowofexternalhistorypaths;sampled/nativetransientwriterlimitsretained. Provenpermanentquarantinesr395/r463/r466/r482unchanged.',root_scope='Documentaryprovenance/integrity/routingonly,no root mathematical solving/programs/Lean/checkers.',credit=0,accepted_new=57,target_new=60,formal_dispatch=False,terminal_self_exclusions=ex)
delta='Completedr487zeroqualifiedsurvivors. '+summary+' NEW ENTIRE BujtasIrsicChenowethKlavzarZhang The d-distance p-packing domination number: complexity, cycles, and trees original2507.18272/finalDOI10.1007/s00010-026-01266-w ALLNEWdeliveryunavailable afterautomaticSpringercookiecycleGUARDREJECTEDBEFORErepeatarticlefetch;failedreceipt/STOPnonPASSpreserved,no manualbypass/retry.120files20bindings13frozen809savedhistorypathsverified,9chargedGET6payloads3redirect1unavailable3search9queries.57/60unchanged.'
den=read(ROOT/'inherited-denials-r493.json');den['utc']=now
den['blocked_keys']=sorted(set(den['blocked_keys'])|{'link.springer.com/article/10.1007/s00010-026-01266-w','doi.org/10.1007/s00010-026-01266-w'})
den['blocked_artifacts']=sorted(set(den['blocked_artifacts'])|{'2507.18272','10.1007/s00010-026-01266-w','the d-distance p-packing domination number'})
den['records'].append(dict(url='https://link.springer.com/article/10.1007/s00010-026-01266-w',reason=dict(status='Automaticcookieauthorize/transitredirectcycleguardrejectedBEFORErepeatarticlefetch',artifact='BujtasIrsicChenowethKlavzarZhang The d-distance p-packing domination number: complexity, cycles, and trees original2507.18272/finalDOI10.1007/s00010-026-01266-w',restriction='ENTIRE identified work ALL NEW hosts,versions,arxiv,authors,caches,mirrors,DOI/API,body/metadata deliveries unavailable. No retries/identity correction/indirect recovery/cookieworkaround. Explicitalready-supplied pre-failurev2 only,notfinalequivalence. Notblanketalltreepapers.'),evidence=dict(path=str(A/'NETWORK-STOP.md'),sha256=sha(A/'NETWORK-STOP.md'),guard_sha256=sha(A/'guard-ledger.jsonl'),receipt_sha256=sha(A/'get-tree-final.receipt.json'))))
den['root_r487_scope']=delta;denpath=ROOT/'inherited-denials-r494.json'
# All integrity checks precede documentary integrations and fresh review construction.
save(P/'expanded-corpus-r487-parent-integration.json',record);save(denpath,den)
assert not R.exists();R.mkdir();(R/'inputs').mkdir();base=P/'expanded-corpus-r433'
for name in ['bootstrap.py','run.py','write_lane.py','verify_frozen.py','registry-roots.json','source_get_guard.py','model-policy-sol-only.json']:shutil.copyfile(base/name,R/name)
shutil.copyfile(ROOT/'charge_search.py',R/'charge_search.py');shutil.copyfile(denpath,R/'inherited-denials.json')
literal=prov['378413']['object'];(R/'inputs/original378413.raw.jsonl').write_bytes(base64.b64decode(prov['378413']['raw_base64'],validate=True));save(R/'inputs/provenance378413.json',prov['378413']);save(R/'inputs/literal378413.json',literal);save(R/'inputs/author-gates378413.json',gates['378413'])
for name in ['FULLCANDIDATE.md','DORMANT-SOL-FORMAL-PLAN.md','NETWORK-STOP.md']:shutil.copyfile(A/name,R/'inputs'/name)
for name in ['zigzag.pdf','zigzag.txt','zigzag-companion.pdf','zigzag-companion.txt','zigzag-page5.png']:shutil.copyfile(A/'sources'/name,R/'inputs'/name)
for name in ['zigzag.json','zigzag-companion.json']:shutil.copyfile(A/'plans'/name,R/'inputs'/('get-'+name))
shutil.copyfile(ROOT/'accepted57-review-context.json',R/'inputs/accepted57-scopes.json');prior=P/'spherical-error-monotonicity-source-review-sol-r1/inputs/prior39-routing.json';assert sha(prior)=='6493e29137d286242b09d96f97dfe39a9ca5146a8d73bcfa8177e4705d6aaff3';shutil.copyfile(prior,R/'inputs/prior39-scopes.json')
save(R/'reservation.json',dict(ids=[378413],rows=[literal],purpose='Independentfinitecubicalcomplex/zigzagcounterexampleandfullsource/prior/significancequalification,noformaltools/selfacceptance'));(R/'reservation.sha256').write_text(sha(R/'reservation.json')+'  reservation.json\n');save(R/'search-budget.json',dict(calls_used=0,queries_used=0,maximum_calls=2,maximum_queries=6,charged_before_call=True))
task=f'''Use ONLY GPT-6.1 Sol, high effort, default speed. Personally and independently review MathDB378413's proposed finite cubical3-complex odd-dimensional zigzag-signature refutation: exact source definitions, every ordinary quotient/flag bridge, prior/final/significance. Current57/60 beyond39prior,96total. Nochildren/fallback/mathematicalprograms/formaltools/selfcredit. Root orchestrates; you do mathematics. Complete bounded review,notacknowledgment/acquisitiononly.

FIRST shell command EXACTLY:
timeout 20 python3 -I -B {R}/bootstrap.py
Read COMPLETE printedTASK/AGENTS. SECOND EXACTLY:
timeout 140 python3 -I -B {R}/verify_frozen.py before
No punctuation/chaining. Bootstrap/standaloneverifiers explicitcapexceptions. Everyother substantive localoperation immutable ABSOLUTE {R}/run.py UNIQUE_LABEL Pythonstdin; authoredwrites immutableABSOLUTE {R}/write_lane.py. Neverrerunbootstrap/editfrozenhelpers/inputs/TASK/caps. Preservefailures/freshdiagnosticrepairs. Actualprotected/frozen/access/guard/counter/capbreach STOP/quarantine/noreset. Documentarytypo/render/serializationfailure notautomaticallypolicybreach.

SOLE378413. Protectedactivepeers expanded-corpus-r488 and split-decomposition-orthogonality-source-review-sol-r1,evenmetadata/stat/read/hash/list/glob/poll/reservations/flatbasenames. NOhistoryallowlist. Ownfrozeninputs/products andexplicitPDFskillonly,noauthorlane/ROOT/campaign/history/embeddedpaths. Allformal/code-loop/Polynexus/crown/bunkbed/tournament/Hat bodiesANDflat integrations protected. ALLr395/r463/r466/r482 packets permanentlyquarantined,noreuse/refetchseeds. Public/server/api/.../contentforbiddenAPIevenPDF-looking/guard200. Allwritesownlane,no/tmp/shared/parent/git/install/publish/accounts/messages. Trusted57+39scopesboundedcontextonly,nocertificateaudit.

Startfromexactraw/literal andactualmath0405279v1 fullintroduction/Definitions2.1-2.7/Conj2.8/proximatehypotheses,allmeaningsofcomplex/dimension/flag/adjacency/T/reversal/signature/typeI/typeII. Readactualsource,notgenericabstractpolytopes/simplicialcomplexes. Iscomplexarbitraryfiniteboundedrankedthinposet,orareconnectivity/flagconnectivity/orientability/spherical/simplicialassumptionsstanding? Determinewhicharedefinitionallyrequiredandpaythemforactualconstruction. Auditmaximalchainlength/rankconventions,source-right-versus-leftactionorderT=sigma_(d+1)...sigma1,whichsigmaalterselement,pairedincidencecount,andwhy sigma1f inTorbitimpliesNONZEROtypeI andsigmanot(0,0). Sourcecorrectionszero,do notreplace exactproblemwithorientable/convexpolytope question.

Use/announce/read PDFskill /home/mj-kang/.codex/plugins/cache/openai-primary-runtime/pdf/26.1103.10131/skills/pdf/SKILL.md; visuallyinspectmaterialactualdefinition/Conj2.8/T/signatureglyphs,notrelyonauthorPNGreport. Sourceotherfiguresonlyifneeded;novisualPASSforunseenpages. NoPDFauthoring/installs. Actual2017v3DezaPankov1509.03754supplied;authorreadonlyselectedpp1-9. ReadrelevantACTUALtheorem/proofandwhatkindofcomplex/simplicity/signaturetheycover;noextrapolationfromvertexshadow/simplicialCoxeter tooldcubicalsignature. Final/corrections/identifiedlengthspaper remainunpaid,notglobalnoveltyveto. DistinctdeniedDezaworks elsewhereintheunionarenotthisoriginalbysharedsurname;inspectexactidentitybeforeacquisition.

Independently reconstructordinaryargument beforetrusting FULLCANDIDATE.md,thenadversariallyauditit. ProposedcoverQ unitcubicalcellsinR3,groupGamma generated100Z3translations andg(x,y,z)=(11-x,y+10,z+10). Needfullgroupnormalform/freeness/minimumdisplacement,finitecellorbits,well-definedpartialorderincludingtransitivity/antisymmetry,globalbottom/top,ranks,purity/allmaxchains. Localface/coface-liftingclaimmustbeproved; merelyfreevertexactiondoesnotguaranteethinquotient. Checkuniformdisplacementboundforeachnonidentitytransform includingevenpowers/cancelledtranslations,starboundingboxanduniquecompatiblelifts,allfourranktwointervaltypeswithnoglobalquotientincidenceextras/identifiedintermediates. Payanystrongerstandingconnectivityconditionratherthanassumegeometricquotientisacceptedposet. Showwell-definedfiniteflagquotient andunambiguousalternativefaceoperators,notunprovedfinitequotientofinfiniteobject.

Flagfhasvertex0,positivexedge,xyface,unitcube. Authorclaims T3f=f+(1,1,1),henceT30f=f+(10,10,10),gf=sigma1T30f andquotient sigma1q(f)=T30q(f). VerifyeveryrankfaceinthreeiterationswithEXACTsourceoperatororder;induction/translationequivariance;gactionreflectiononedge/face/cube;commutationwithoperators;distinctflagendpoints;finiteT-permutation/orbitandcountedtypeIcriterion. Notenoughnumericalvertexidentity,equalityofallflagcellsrequired. Needfinite3dimcomplexandgenuinepositivecount,notboundarydimension1orundefinedorientedintersection. RepairgapsconcretelyorpreciseGAP;no silentweakening/newassumptions. No claimallorbitlengths/wholesignatureunlesspaid.

Scientificgatecentral:strongpositivecase finiteproperlocalcubical3-manifold underexplicitarbitrarythincomplexdefinition defeatsfullprintedodd-dimensionalconjecture,notlowdimendpoint. Strongcontrarycase nonorientableglidequotient exploitsmissingorientation/spherical/intendeddomain,source/companionmaymakeitdomaincorrectionexcludedbycampaign. Determineactualcontent,notshortness or openlabel. Standardglidequotientaloneisnota completeprior-to-thissigmacertificatebridge. Ifclaimroutineprior,readactualapplicableprimarytheorem/proofandgiveCOMPLETEquotient/signaturebridge. Ifdomaincorrection,saypreciselywhyfromactualsourceevidence,notinventedorientationassumption. Ifsubstantive,identifymissingnewlemmataandwhyactualearlierresultsnotfullsubsumer. No worldwideabsenceclaimfromboundedsearch/no genericnoveltyveto;identifiedmatchingunreadproofispreciseHOLD.

Compareall57+39suppliedexactscopesonly:sharedschedule/parity/cube/finitegraphwordsarenotduplicates;allglide/period/dimension/zigzagvariantsonefamily,helpers/formalization/parameter/source/domain/endpointcorrections/public/routineoutcomeszero. Neighbor378416joinofsimplexboundariesand378417trialityarenotthistarget,notreadfromhistoryorassumedsame. No otherlaneaccess. ConditionaldormantSolbriefonlyiffullordinaryliteral/scientificgates survive,withfinitethinposet/flagpermutation/deckquotient/signature/literalnegationbridges;noimplementation/dispatch. Nomathematicalprograms/enumeration/numericaltests/CAS/solver/Lean/compiler/checker/formalAPI. Personalordinaryreasoningonly;documentary/hash/source/PDFprocessingallowed.

NetworkreadENTIREinherited-denials/recovermaterialtruncations BEFORErequests. SoleGETimmutable source_get_guard.py UNDERrun.py,ONEmanuallyselectedexactpersistedplan/invocation,url/routes/destination/source_identity/purpose,route['378413'],NEWownsourcesdestination,identity/purpose>=12chars. Max8GETHOPSincludingredirects;max2nativeSEARCHcalls6exactquerystrings. BeforeEACHsearchpersistqueries-listplanviawriter,readLIVEcounter/ledger,prechargeimmutableABSOLUTEcharge_search.py underrunner,neverreset/refund/manualcounteredits. SaveFULLactualresponseimmediatelybeforeotherwork,ordinaryJSON/string,no btoa/TextEncoder;recoverSAMEinmemoryresponsewithoutanothercallonlocalserializationfailure. Searchnavigationnotproof.
NoAPIincludingpublic/server/api bitstreams,customHTTP/curl/wget/requests/HEAD/nativeopenfetch/browser/accounts/POST/TLS/cookie/JS/meta-refreshworkaround. EveryfailureidentifiedworkALLNEW hosts/versions/arxiv/authors/caches/mirrors/DOI/API/body/metadata deliveriesunavailable,noretry/identitycorrection/indirectrecovery. Allinheritedblocksapply,including2507.18272treeDOI10.1007/s00010-026-01266-w,math0601731polydigraph,0704.0541fixedunitsums,1106.5068EPSand2014Poly-antimatroidpolyhedra. Cachedexplicitpre-failurecopiesonlynotfinalequivalence;distinctotherpapersnotblanketdenied. Fourregistryrootmetadataartifactsunavailable,norefresh/reconstructionviaREADME/tree/API/branch/version. Guardhistoryunchanged;transport200nonpaperclassifiedseparately.

Processgenesislimit:authorr487networkSTOP/failurepreservedafterautomaticSpringercookiecycle onUNRELATEDtreework. Rootverifiedguardpreventedrepeatedarticlefetchbeforedispatch;threeautomaticarticle/authorize/transitrequestscharged,nomanualretry/cookieworkaround/reset/protectedread/APIacquisitionestablished. Pre-stop378413source/ordinaryevidencecopiedunacceptedforindependentreview;thisisnotrootuniversalprocedurePASSorwaiverofprovenbreaches. DoNOTtouch/retrythatwork orclaimfinalequivalence,editledgersorotherlane. Independentlyauditcopyboundaries/taskprocess,reportcandidlimits. Standalonesourcefrozenbefore/aftermandatory.

Capsaffinity<=2,childCPU115/supervisor120,AS6GiB,sampledgroupRSS6GiB,deadline130/outer140,arena2. Allsynchronousrunnerreceiptsactualresources/reaping,nobackgroundjobs. StandaloneverifierCPU120exceptionnotnestedunderchild115. Native/transient/writer/supervisorpeaksunknown,nouniversalcomplianceclaim.

Deliver REVIEW.md,independentPROOF.mdorpreciseGAP.md,keyedreview.json378413 separateliteral/source/ordinary/prior/novelty/significance/family/formal/independent/procedure/acceptancegates,fullsource-map/opposingcases,read/visual/access/search/resourceinventories,actualreceipts/hashmanifest. Final standalonefrozen-after THENmanifestEVERYownfile/helpers/frozeninputs/plans/payloads/fullresponses/ledgers/ALLcompletedreceiptJSON,preciselynamedterminalnoncircularexclusions,nolaterfrozenwrites. Completeboundedreviewordocumentprecisegaps. Credit0,57/60unchangeduntilrootacceptance.
'''
(R/'TASK.txt').write_text(task);files=[q for q in R.iterdir() if q.is_file() and q.name!='search-budget.json']+list((R/'inputs').iterdir());save(R/'frozen-inputs.json',{str(q):sha(q) for q in files})
ready=dict(utc=now,lane=str(R),mathdb_id=378413,task_sha256=sha(R/'TASK.txt'),frozen_bindings=len(files),model='gpt-6.1-sol',reasoning='high',service='default',accepted_new=57,credit=0,protected_peers=['expanded-corpus-r488','split-decomposition-orthogonality-source-review-sol-r1'],source_copy_scope='Cleanr487target-onlyliteral/provenance/authorproposal/cachedpre-stopzigzagsourceanddistinctcompanion/57+39scopes;unrelatednetworkSTOPretained,nouniversalprocedurePASS')
save(ROOT/'cubical-zigzag-review-r1-ready.json',ready);save(ROOT/'selection-routing-cubical-zigzag-review-r1.json',dict(ids=[378413],sources=[literal['source_url'],'https://arxiv.org/abs/1509.03754'],lane=str(R),task_sha256=ready['task_sha256'],metadata_only=True));save(ROOT/'r487-completion-boundary-delta.json',dict(utc=now,message=delta,new_protected_peer=R.name,immutable_worker_inputs_unchanged=True))
print(json.dumps(dict(manifest_files=120,frozen_bindings=13,original_bindings=20,receipt_exit_counts=record['receipt_exit_counts'],review=ready)))
