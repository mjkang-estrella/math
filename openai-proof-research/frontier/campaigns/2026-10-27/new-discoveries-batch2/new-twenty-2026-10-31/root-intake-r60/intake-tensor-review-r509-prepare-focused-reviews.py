"""Root integrity, routing and documentary qualification only; no mathematical solving."""
import os,resource
os.sched_setaffinity(0,sorted(os.sched_getaffinity(0))[:2])
resource.setrlimit(resource.RLIMIT_CPU,(120,120))
resource.setrlimit(resource.RLIMIT_AS,(6*1024**3,6*1024**3))
from pathlib import Path
import json,hashlib,datetime,re,collections,ast,base64,shutil
ROOT=Path(__file__).resolve().parent;P=ROOT.parent;chunks={}
t=ast.parse((ROOT/'intake-planar-review-r506-prepare-r508-r509.py').read_text())
exec(compile(ast.Module(body=[x for x in t.body if isinstance(x,ast.FunctionDef)],type_ignores=[]),'<documentary-functions>','exec'),globals())
now=datetime.datetime.now(datetime.timezone.utc).isoformat();assert read(P/'ledger.json')['accepted_new']==57
R=P/'tensor-dominant-orbit-source-review-sol-r1';A=P/'expanded-corpus-r509'
m=read(R/'SHA256-MANIFEST.json');assert len(m['entries'])==77
names=set()
for x in m['entries']:
 n=x['path'];assert n not in names and not Path(n).is_absolute() and '..' not in Path(n).parts;names.add(n)
 q=R/n;assert not q.is_symlink() and sha(q)==x['sha256'] and q.stat().st_size==x['bytes']
ex=m['exclusions']['excluded'];assert set(ex)=={'SHA256-MANIFEST.json','terminal_seal.receipt.json','terminal_seal.output.txt'}
actual=set()
for q in R.rglob('*'):
 assert not q.is_symlink()
 if q.is_file():actual.add(str(q.relative_to(R)))
assert actual==names|set(ex);frozen(R,32);rrec=receipts(R,{})
assert sha(R/'TASK.txt')==read(ROOT/'tensor-dominant-orbit-review-r1-ready.json')['task_sha256']
prov=read(R/'inputs/provenance323694.json');raw,obj,token=corpus(prov)
assert raw==(R/'inputs/original323694.raw.jsonl').read_bytes() and obj==read(R/'inputs/literal323694.json')==read(R/'reservation.json')['rows'][0] and obj['mathdb_id']==323694
assert token.decode()==prov['statement_token'] and dg(token)==prov['statement_token_sha256'] and dg(obj['statement'].encode())==prov['statement_utf8_sha256']
family=read(R/'family-comparison96.json');assert family['count']==len(family['comparisons'])==96 and all(x['actual_scope_fields'] and x['comparison'] for x in family['comparisons'])
review=read(R/'review.json');assert review['323694']['decision']=='ORDINARY_PASS_SCIENTIFIC_HOLD_NO_DISPATCH'
assert read(R/'search-budget.json')==dict(calls_used=0,queries_used=0,maximum_calls=2,maximum_queries=6,charged_before_call=True)
assert 'guard-ledger.jsonl' not in actual and 'search-charges.jsonl' not in actual
source=read(R/'source-map.json');assert sha(R/source['sources'][0]['local'])==source['sources'][0]['sha256']=='0ef23e0ad701cdfd6237c13ce9baf7fd602a72dd7f23e252c310247d3cd5be44'

route=read(ROOT/'selection-routing-r509.json');assert sha(A/'TASK.txt')==route['task_sha256'] and sha(A/'reservation.json')==route['reservation_sha256']
aex=manifest(A,'MANIFEST.json',170,'terminal_manifest','self_exclusions');frozen(A,13);arec=receipts(A,{})
budget=search(A,3,9,3,9,['search1-response.json','search2-response.json','search3-response.json'])
ids=read(A/'reservation.json')['ids'];gates=read(A/'results.json');assert len(ids)==20 and set(ids)==set(map(int,gates))
provenance=read(A/'originals.json');assert len(provenance)==20;sources={}
for v in provenance:
 raw,obj,token=corpus(v);mid=v['id'];assert obj['mathdb_id']==mid and mid in ids and mid not in sources
 assert base64.b64decode(v['raw_base64'])==raw and v['object']==obj and (A/'literals'/f'{mid}.jsonl').read_bytes()==raw
 assert len(v['statement_tokens'])==1;z=v['statement_tokens'][0]
 assert z['token']==token.decode() and z['token_sha256']==dg(token) and z['decoded']==obj['statement']==gates[str(mid)]['literal'] and z['decoded_sha256']==dg(obj['statement'].encode())
 sources[mid]=obj['source_url']
events=guard(A,list(A.glob('get-*-plan.json')),ids,dict(attempt=5,success=5),3)
history=read(A/'history-access.json');allow=read(A/'historical-results-allowlist.json');assert len(history)==865
for x in history:
 rel=Path(x['path']).relative_to(P)
 assert not any(t in part.lower() for part in rel.parts for t in ['formal','code-loop','code_loop','polynexus','crown','bunkbed','tournament','hat-bipartite'])
 assert not any(f'expanded-corpus-r{z}' in x['path'] for z in [395,463,466,482]) and x['path'] in allow and allow[x['path']]==x['sha256']
manual=read(A/'NEW-UNAVAILABLE.json');page=A/'sources/current-ai-claims.html'
assert manual['url']=='https://aimath.robertj1.com/' and page.read_bytes().find(b'challenge-platform')==manual['raw_byte']==6100241
assert not any('aimath.robertj1.com' in x for x in read(A/'inherited-denials.json')['blocked_keys'])
rs='323694 independent cachedliteral/fullordinary PASS: unique actual product-group rank4 orbit everyp>=4,exactframecount,defect15*2^-p,all96trustedscopesboundednonmatch. ROOT retains scientificHOLD,not routine/public exclusion: reviewer supplies complete mathematical normal-form/frame/hyperplane-to-target reduction but original source prints matrix normal forms/GLcount without earlier subsuming proof authentication; hyperplane rankone-spanning bridge notprinted there. Actual Sumi-Miyazaki-Sakata LAA431(2009)1858-1868 andJaJa SIAMJComput8(1979)443-462 cited bodies unread/no finitefieldall-p theorem authenticated. Strong routine objection and deliberateall-p sourceconjecture positivecase both preserved,focusedprimary/significance reviewassigned. All6materialsourcepagesviewed;originalv1only/no finalcorrection,currentprior/registrycleared.77ownmanifestfiles32frozen1corpusbinding96scopecomparisons verified;0freshGET/search,14runnerreceiptsall0;fullinheriteddenialsnotpersonallyrecovered so no requesteligible/made. No formaldispatch or credit.'
ass='r509 zeroqualifiedsurvivors.338806 AUTHOR fullall-g finitebipartite counterexampleproposal atfixedDelta100/epsilon1/4; actualv2literal/readvisualpass claimed, independentordinary/sourcefinal/prior/significance/family/formalunpaid,assignedindependentreview. EmptyrectanglefromURmatchingDAG,100independentpermutations,noholeprobability,explicitshortcycle/parallelwitnessdeletion,retainedmatching>0.99N,UR<N/2; no rootmathematicalassessment.356838 incidencecyclebalancedrealization/residuesurgery unpaid;376155 actual2607.18964v3 strongerpublictheoremproofbridgezero. Other17originalsunread.170ownmanifestfiles20corpusbindings13frozen865savedhistorynames verified;5GETsuccess3PDF2HTML,3search9strings. NEW distinctaimath.robertj1.com currentAIclaims exactindexchallenge atbyte6100241 manuallyclosed,transport200/guardunchanged,no novelty/nohitclearance;not inherited4rootretry,not blanketprimarypaperban. Output/materialrecovery andunknownnative/transient/writerlimitsretained.'
recR=dict(utc=now,mathdb_id=323694,source_lane=str(R),task_sha256=sha(R/'TASK.txt'),manifest_sha256=sha(R/'SHA256-MANIFEST.json'),verified_manifest_files=77,verified_frozen_bindings=32,verified_original_bindings=[323694],verified_saved_scope_comparisons=96,review=review,source_map=source,runner_receipts=rrec,scientific_summary=rs,root_disposition='ORDINARY_PASS_SCIENTIFIC_HOLD_FOCUSED_PRIMARY_REVIEW_ASSIGNED',credit=0,accepted_new=57,formal_dispatch=False,terminal_self_exclusions=ex)
recA=dict(utc=now,source_lane=str(A),task_reservation_genesis_verified=True,manifest_sha256=sha(A/'MANIFEST.json'),verified_manifest_files=170,verified_original_bindings=ids,verified_frozen_bindings=13,source_url_by_id=sources,all20_gates=gates,runner_receipts=arec,guard_events=dict(collections.Counter(e['event'] for e in events)),search_budget=budget,verified_saved_history_names=865,scientific_summary=ass,root_disposition='ZERO_QUALIFIED_SURVIVORS_338806_INDEPENDENT_REVIEW_ASSIGNED',credit=0,accepted_new=57,formal_dispatch=False,terminal_self_exclusions=aex)
den=read(ROOT/'inherited-denials-r519.json');den['utc']=now;den['root_tensor323694_review_scope']=rs;den['root_r509_scope']=ass
den['blocked_keys']=sorted(set(den['blocked_keys'])|{'aimath.robertj1.com'})
den['blocked_artifacts']=sorted(set(den['blocked_artifacts'])|{'aimath.robertj1.com current ai claims index','open math problems claimed to be solved with ai current registry index'})
den['records'].append(dict(url=manual['url'],reason=dict(status='Manualchallenge;transport200/guardsuccessunchanged',artifact=manual['entire_artifact'],restriction=manual['restriction']),evidence=dict(path=str(A/'NEW-UNAVAILABLE.json'),sha256=sha(A/'NEW-UNAVAILABLE.json'),payload_sha256=sha(page),guard_sha256=sha(A/'guard-ledger.jsonl'))))
# All documentary checks precede root mutations. No root mathematics or new network.
save(P/'tensor-dominant-orbit-source-parent-integration-r1.json',recR);save(P/'expanded-corpus-r509-parent-integration.json',recA);denpath=ROOT/'inherited-denials-r520.json';save(denpath,den)
common_tree=ast.parse((ROOT/'prepare-covariance-planar-reviews-r506.py').read_text());common=next(ast.literal_eval(x.value) for x in common_tree.body if isinstance(x,ast.Assign) and any(isinstance(y,ast.Name) and y.id=='COMMON' for y in x.targets))
NAMES=['tensor-dominant-orbit-primary-qualification-sol-r2','high-girth-ur-matching-source-review-sol-r1']
DETAILS={323694:'''FOCUSED O1/O2/O3 qualification of323694, not another generic proof replay. Earlier independent full ordinary/sourcev1 PASS and96scopeboundednonmatch are supplied evidence. Trust that bounded review without upstream/certificate audit; personally inspect the exact action/rank/uniqueorbit/count bridge insofar as needed for the primary comparison. This target-specific instruction supersedes repeated full96comparison/reconstruction in generic boilerplate unless scope changes. O1: actual current final/version/correction status of Bremner-Hu1206.5179; cachedv1/nojournal does NOT certify absence. Originalwork notknownclosed; obeyfullunionbeforeanyrequest,do not needlessreacquire cachedbody. O2: personally read ACTUAL primary theorem AND proof of Sumi-Miyazaki-Sakata Rank of3-tensors with2slices andKronecker canonical forms,LAA431(2009)1858-1868, orJaJa Optimal evaluation ofpairs ofbilinear forms,SIAMJComput8(1979)443-462, if applicable. These are authenticated reference entries only, no observed bodyURL or matching theorem yet. Authenticate observed primary URLs/navigation, no guessed URL/field/format. Pay all-p BINARY F2,productGLp xGL2 xGL2,ordinarytensor rank/unique rank4,not complex/real/matrix-rank surrogate. If theorem applies, COMPLETE hypothesis/conclusion-to-original-limit reduction includinghyperplane rankone generation,fullproductaction,exactcount or asymptotic,not abstractsimilarity. If notapplicable giveconcrete theorem-levelnonmatch with actualhypotheses,not snippet.
O3 significance: previousreview has complete mathematical normal-form/frame/hyperplane bridge, but source states classicalmatrixnormalforms/finiteGLorder without primaryproof; current reconstructed proof doesnotauthenticate earlier subsumingprimaryproof. Strongnegative: rankone/ranktwo dualcoefficient normalforms plus twoexplicit3rankone hyperplanebases may be complete routine application. Strongpositive: exactexplicit2012all-pconjecture,uniqueactualtensor-rank4orbit,structuralhyperplanebridge,exactcount/exponentialerror. No exclusionfor shortness/familiarity/openlabel alone. Give reasoned bounded prospectivequalification OR complete routine/publicbridge OR preciseunpaidgate; distinguish exactearlierprintedsolution,new routine reduction and domaincorrection. Do not silentlytreatno externalproof as novelty or genericworldwideunknownasautomaticveto. Actualprimaryproof required before routine/publicexclusion undercampaignrules.
Exactendpoint: forp>=4 orderedindependent4columns formoneactualorbit viaGLp alone; simpletensor expansion givesrank<=4,flatteninggives>=4; deficientslice spanliesinM2hyperplane,dualactionB^-t C D^-1 reducesCtoE11orI; rankonebasesE12,E21,E22orE12,E21,J implyrank<=3. Countproduct_j=0..3(2^p-2^j),fractiondefect<=15*2^-p. Matrixcolumnoperationsinrankproofarenotallowedtensorsymmetries. Earlierreviewpaidallboundaries,notten-orbitConj1. No formaldispatch. ConditionaldormantSolbriefonlyifscientificprospectivegatesclear,otherwise exactGAP. Ownprior-review files are copied evidence; noROOT/oldlane/embeddedpathaccess. Narrow380362metadataadjudicationistrustedroutingonly,notpartofO1-O3 investigation.
''',338806:'''Independent full ordinary proof, literal/source/final and substantive qualification of338806 High-girth approximation for uniquely restricted matching number,1803.11032v2. Literal: forall epsilon>0,positiveintegerDelta,existspositiveg,forallfinite simpleundirectedG withmaxdegree<=Delta,girth>=g,nu_ur(G)>=(1-epsilon)nu(G). Audit sourcep1definitions andConj1.4p3,all9pagesstandinghypotheses: notsilentlysubcubic/connected/regular/bipartite-only; uniquelyrestricted means no DISTINCT matching coversexactlysamevertices,notinducedmatching. Authorclaims fixedDelta100,epsilon1/4 andFOREVERYg finitebipartitecounterexample. This refutes actualintendedlargegirthregime,notfiniteg/degreegrowing/subdivisioncorrection. ActualfinalGraphsCombinatorics35(2019)353-361 DOI10.1007/s00373-018-1991-8 identifiedbyactualsavedsearchbutNOTrequested; originalworknotknownclosed. Inspectobservedactualprimaryrouteonly,notguessedalternate; iffailureentireworkclosesno recovery. Cachedoriginalv2/metadata notfinalequivalence. Materialsourceglyphsviewpersonally.
Reconstruct proof beforeauthorFULL. Mechanismdisclosed: bipartiteURmatchingM size m definesdigraphonmatchededges i->j ifx_i y_j anedge,i!=j. Directedcyclegivesdifferentmatchingonsamecoveredvertices; URimpliesDAG. Topologicalorder givesemptyrectangle:lastfloor(m/2) matchedX andfirstfloor(m/2) matchedY. Payorderorientation/disjointindices,notjustacyclicunderlyinggraph orassumedperfectmatching.
Construction: d100independentuniformbijections betweenN-by-N sides,4|N,initialcoloredmultigraph. Fixeda=N/4 setsA,B avoidedbyonepermutationwithprobability(N-a)_a/(N)_a<=exp(-N/16). Independentcolors andatmost4^Nchoicesgivebad-hole probability<1/4 forlargeN. Explicitcoloredclosedcyclewitnesses length2l,l1..h=max(1,ceil(g/2)); l1twodistinctcolorssamepairparallelwitness,l>=2distinctXandYanddistinctcolorededges. Count<=N^(2l)d^(2l); consistentr prescribedpairsinonecolorprobability1/(N)_r,conflictprob0;N>=4h givesexpectationW_l<=(2d)^(2l). S=sum2lW_l,B_h=sum2l200^(2l),finitegconstant. Choose4|N,N>400B_h andotherbounds; MarkovPr(S>=N/100)<1/4; unionbad<1/2 =>existstuple. No conditioningonlargegirth,importedexpander theorem or numericexperiment.
Deleteeveryvertexofeveryshortcoloredwitness,atmostS; inducedremaininggraphsimple,maxdegree<=100,noordinarycycle<=2h,girth>=g includingforestconvention. No largeemptyrectanglecanappearamongSURVIVORS byinduceddeletion; notedgedeletion. Firstcolorperfectmatchingloses<=deletedvertices edges,so nu>N*99/100 despiteunequalsurvivingsides. IfUR m>=N/2,4|N givesfloor(m/2)>=N/4;emptyrectanglecontradictsnohole. Thusnu_ur<N/2<(3/4)nu. Pay allfinitecounting/probability/expectation/witnessmultiplicity/l1parallel andgsmallcases,strictinequalities/existence/nonvacuity. Do NOT substitute Chernoff/regulargraphconditioning/claimedexpansionwithoutproof. No mathematicalprograms/enumeration allowed.
SIGNIFICANCE: strongestpositive fullintendeduniformbounded-degreeall-girthrefutation,notendpoint/domain/largeDeltaerror. Strongnegative conventionalhighgirthbipartiteexpansionplusacyclicmatchingobstructionmayhavecompleteearlierprimarybridge. Actual applicable theorem AND proof plusfullconstant/hypothesis/induceddeletion/ratio-to-literal reduction required forroutine/publicexclusion; standardprobabilisticingredientsorbriefproofalone insufficient. Searchactualuniquelyrestrictedmatching/highgirthprior claims. Distinguish induced/acyclic/uniquematchingdefinitions and lowerboundssubcubic fromtargetallDelta. All96trustedscopecomparepersonal,notopicmatching. Noearlierexactcounterexampleauthenticated; boundedpriornotworldwidenovelty. ConditionalfullliteralformalplanonlyifscientificprospectivePASS; no formaltoolsnow.
New exactAIclaimsindexaimath.robertj1.com closedbychallengeatrawbyte6100241;ALLNEWindexbody/METADATA/query/host/version/cache/mirror/API/indirectdeliveries unavailable. Transport200guardsuccessunchanged,noindexnohit/noveltyclearance. This wasDISTINCT fromfourinheritedclosedregistryroots,notauthorretry; no blanket primarypaperban. Youreceive onlytargetproof/source/navigationevidence,nochallengepayload. No newindexrequestorindirectreconstruction.
'''}
readies=[]
for mid,name in [(323694,NAMES[0]),(338806,NAMES[1])]:
 L=P/name;assert not L.exists();L.mkdir();(L/'inputs').mkdir()
 for helper in ['bootstrap.py','run.py','write_lane.py','verify_frozen.py','registry-roots.json','source_get_guard.py','model-policy-sol-only.json','charge_search.py']:shutil.copyfile(R/helper,L/helper)
 shutil.copyfile(denpath,L/'inherited-denials.json')
 if mid==323694:
  for f in ['original323694.raw.jsonl','literal323694.json','provenance323694.json','author-gates323694.json','FULLCANDIDATE.md','tensor.pdf','tensor.txt','tensor-meta.html','search1-response.json','search2-response.json','search3-response.json']:shutil.copyfile(R/'inputs'/f,L/'inputs'/f)
  for f in ['REVIEW.md','PROOF.md','review.json','source-map.json','family-comparison96.json','read-access-inventory.json']:shutil.copyfile(R/f,L/'inputs'/('prior-review-'+f))
  literal=read(R/'inputs/literal323694.json')
 else:
  raw=(A/'literals/338806.jsonl').read_bytes();literal=json.loads(raw);(L/'inputs/original338806.raw.jsonl').write_bytes(raw)
  save(L/'inputs/literal338806.json',literal);save(L/'inputs/provenance338806.json',next(x for x in provenance if x['id']==mid));save(L/'inputs/author-gates338806.json',gates[str(mid)])
  for f in ['FULLCANDIDATE.md','DORMANT-SOL-FORMAL-PLAN.md','source-read-inventory.json','search1-response.json','search2-response.json','search3-response.json','get-matching-plan.json','get-matching-metadata-plan.json']:shutil.copyfile(A/f,L/'inputs'/f)
  for f in ['matching.pdf','matching.txt','matching-metadata.html']:shutil.copyfile(A/'sources'/f,L/'inputs'/f)
 for f in ['accepted57-scopes.json','prior39-scopes.json']:shutil.copyfile(R/'inputs'/f,L/'inputs'/f)
 save(L/'reservation.json',dict(ids=[mid],rows=[literal],purpose='Focused independent primary/source/proof/significance qualification; no formal tools'))
 (L/'reservation.sha256').write_text(sha(L/'reservation.json')+'  reservation.json\n');save(L/'search-budget.json',dict(calls_used=0,queries_used=0,maximum_calls=2,maximum_queries=6,charged_before_call=True))
 peers=[x for x in NAMES if x!=name]+['expanded-corpus-r510']
 task=common.format(lane=L,id=mid,peers=', '.join(peers))+'\nTARGET-SPECIFIC INSTRUCTIONS (override repeated review only where explicit)\n'+DETAILS[mid]
 (L/'TASK.txt').write_text(task);frozenfiles=[q for q in L.iterdir() if q.is_file() and q.name!='search-budget.json']+list((L/'inputs').iterdir());save(L/'frozen-inputs.json',{str(q):sha(q) for q in frozenfiles})
 ready=dict(utc=now,lane=str(L),mathdb_id=mid,task_sha256=sha(L/'TASK.txt'),frozen_bindings=len(frozenfiles),model='gpt-6.1-sol',reasoning='high',service='default',accepted_new=57,credit=0,protected_peers=peers)
 slug='tensor-dominant-orbit-qualification-r2' if mid==323694 else 'high-girth-ur-matching-review-r1'
 save(ROOT/(slug+'-ready.json'),ready);save(ROOT/('selection-routing-'+slug+'.json'),dict(ids=[mid],sources=[literal['source_url']],lane=str(L),task_sha256=ready['task_sha256'],metadata_only=True));readies.append(ready)
save(ROOT/'tensor-review-r509-completion-boundary-delta.json',dict(utc=now,summary=rs+'\n'+ass,new_protected_peers=NAMES,immutable_worker_inputs_unchanged=True,credit=0,accepted_new=57))
print(json.dumps(dict(review_files=77,discovery_files=170,frozen=45,corpus_bindings=21,scope_comparisons=96,readies=readies,credit=0,accepted_new=57)))
