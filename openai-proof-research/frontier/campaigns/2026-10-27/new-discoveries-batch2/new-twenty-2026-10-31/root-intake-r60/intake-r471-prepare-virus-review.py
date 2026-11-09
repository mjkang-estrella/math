"""Root documentary intake and independent source-review preparation only."""
import os,resource
os.sched_setaffinity(0,sorted(os.sched_getaffinity(0))[:2])
resource.setrlimit(resource.RLIMIT_CPU,(120,120));resource.setrlimit(resource.RLIMIT_AS,(6*1024**3,6*1024**3))
from pathlib import Path
import json,hashlib,datetime,collections,re,base64,shutil
from urllib.parse import urlsplit,unquote
P=Path(__file__).resolve().parent.parent;ROOT=P/'root-intake-r60';A=P/'expanded-corpus-r471';R=P/'virus-path-threshold-source-review-sol-r1'
def sha(q):return hashlib.sha256(q.read_bytes()).hexdigest()
def dg(b):return hashlib.sha256(b).hexdigest()
def save(q,v):
 assert not q.exists(),str(q)
 q.parent.mkdir(parents=True,exist_ok=True);q.write_text(json.dumps(v,indent=2)+'\n')
now=datetime.datetime.now(datetime.timezone.utc).isoformat();assert json.loads((P/'ledger.json').read_text())['accepted_new']==57
routing=json.loads((ROOT/'selection-routing-r471.json').read_text());assert sha(A/'TASK.txt')==routing['task_sha256'] and sha(A/'reservation.json')==routing['reservation_sha256']
manifest=json.loads((A/'manifest.json').read_text());entries={x['path']:x for x in manifest['files']};assert len(entries)==145
for n,v in entries.items():
 assert not Path(n).is_absolute() and '..' not in Path(n).parts
 q=A/n;assert not q.is_symlink() and sha(q)==v['sha256'] and q.stat().st_size==v['bytes'],n
exclusions=manifest['terminal_non_circular_exclusions'];assert {str(q.relative_to(A)) for q in A.rglob('*') if q.is_file()}==set(entries)|set(exclusions)
frozen=json.loads((A/'frozen-inputs.json').read_text());assert len(frozen)==13 and all(Path(n).parent==A and sha(Path(n))==h for n,h in frozen.items())
after=json.loads((A/'frozen-after.json').read_text());assert after['count']==13 and after['mismatches']==[]
reservation=json.loads((A/'reservation.json').read_text());ids=reservation['ids'];gates=json.loads((A/'results.json').read_text());prov=json.loads((A/'literal-provenance.json').read_text());assert len(ids)==20 and set(ids)==set(map(int,gates))==set(map(int,prov))
chunks={};sources={}
for key,row in prov.items():
 q=Path(row['chunk']);assert q.is_relative_to(P.parent/'lanes/pi-mathdb-full-corpus-inventory-r301/corpus')
 if str(q) not in chunks:
  b=q.read_bytes();chunks[str(q)]=(dg(b),b.splitlines(keepends=True))
 h,lines=chunks[str(q)];assert h==row['chunk_sha256'];raw=lines[row['line']-1]
 assert dg(raw)==row['raw_sha256'] and row['newline'] is True and raw.endswith(b'\n') and base64.b64decode(row['raw_b64'],validate=True)==raw
 obj=json.loads(raw);assert obj==row['record'] and obj['mathdb_id']==int(key) and gates[key]['record']==obj;sources[key]=obj['source_url']
 for field,value in row['tokens'].items():
  token=re.search(('"'+re.escape(field)+'"\\s*:\\s*("(?:[^"\\\\]|\\\\.)*")').encode(),raw)[1]
  assert base64.b64decode(value['raw_token_b64'],validate=True)==token and dg(token)==value['token_sha256']
  assert json.loads(token)==value['decoded']==obj[field] and dg(obj[field].encode())==value['decoded_sha256']
receipts=[]
for q in sorted(A.glob('*.receipt.json')):
 v=json.loads(q.read_text());assert v['cwd']==str(A) and v['cpu_limit_s']==115 and v['as_limit_bytes']==6*1024**3 and v['deadline_s']==130
 receipts.append(dict(path=q.name,sha256=sha(q),exit=v['exit']))
assert json.loads((A/'finalize-manifest-39.receipt.json').read_text())['exit']==0
budget=json.loads((A/'search-budget.json').read_text());assert budget['calls_used']==3 and budget['queries_used']==9
charges=[json.loads(s) for s in (A/'search-charges.jsonl').read_text().splitlines()];assert len(charges)==3
previous=dict(calls_used=0,queries_used=0,maximum_calls=3,maximum_queries=9,charged_before_call=True)
for i,c in enumerate(charges,1):
 assert c['sequence']==i and c['before']==previous and sha(A/c['plan'])==c['plan_sha256'] and json.loads((A/c['plan']).read_text())['queries']==c['queries']
 expected=dict(previous);expected['calls_used']+=1;expected['queries_used']+=len(c['queries']);assert c['after']==expected;previous=expected
 assert json.loads((A/f'search-response-{i}.json').read_text())
assert previous==budget and sha(A/'charge_search.py')==sha(ROOT/'charge_search.py')
events=[json.loads(s) for s in (A/'guard-ledger.jsonl').read_text().splitlines()];counts=collections.Counter(e['event'] for e in events);assert counts==dict(attempt=11,success=9,redirect=2)
for e in events:
 if e['event']=='success':assert sha(A/e['destination'])==e['sha256'] and (A/e['destination']).stat().st_size==e['bytes']
wdwf=next(e for e in events if e['event']=='success' and e['destination']=='sources/wdwf.pdf');payload=(A/wdwf['destination']).read_bytes();assert not payload.startswith(b'%PDF') and b'<html' in payload.lower() and 'deepayan.chakrabarti' in wdwf['url']
unavailable=json.loads((A/'new-unavailability.json').read_text());assert unavailable['requested']=='https://www.cs.cmu.edu/~deepay/mywww/papers/srds03.pdf'
history=json.loads((A/'history-access.json').read_text());assert len(history)==772;forbidden=('formal','code-loop','polynexus','crown','bunkbed','tournament','hat-bipartite')
assert all(not any(t in part.lower() for t in forbidden) for x in history for part in Path(x['path']).relative_to(P).parts)
audit=json.loads((A/'access-inventory-audit.json').read_text()) if (A/'access-inventory-audit.json').is_file() else None
record=dict(utc=now,source_lane=str(A),manifest_sha256=sha(A/'manifest.json'),verified_manifest_files=145,verified_original_bindings=sorted(ids),verified_frozen_bindings=13,source_url_by_id=sources,routing_pins='Actual task/reservation hashes match retained ROOT genesis',runner_receipts=receipts,receipt_exit_counts=dict(collections.Counter(str(x['exit']) for x in receipts)),guard_events=dict(counts),search_budget=budget,search_counter_continuity='Live old/new states, exact plan digests/querystrings, final counter/helper authenticated; full saved responses parsed',root_disposition='ZERO_QUALIFIED_SURVIVORS_322479_AUTHOR_P4_PROPOSAL_ASSIGNED_INDEPENDENT_REVIEW',scientific_summary='322479authorordinaryP4rationalweightedmapnegation a1/2,b3/10 andallpathssecondary samefamily retained, notindependentPASS. Actual1111.0531v2Conj5.2 and2212.05733v2Th4.1sameexplicitmap sourceconflict, laterTakigawaSection4READ notunreadHOLD. Sourceparameter/visualthreshold/final/corrections/significance/prior unpaid, WDWF2003specificbodyunavailable, no authenticatedroutineexclusion.321481sourceownC12,2 connectedZagrebcounterexample counts198/19>208/20public0;319771actualBranden1004.1382v3publicpowerdeterminantrefutation withnormalization/PSD/rankbridge0, notfreshstability/Ingletonproofaudit.319943universalreducednumeratorvalley noncancellation and321731arbitraryproductlocatingpalette+3 gaps;320173scalingnotgenuinefour2pointmidpoint witness/no degeneracycredit. Sixoriginalsreadfourteenunread.',all20_gates=gates,new_unavailability=unavailable,process='WDWFroute transport200authorhomepage classified nonpaper,separatemanualunavailabilityrecord, guardhistory unchanged. Nine transportpayloads include thisnonpaper/eightactualPDFs. No reportedlocalnonzero; truncationsrecovered, native/transient/writerpeak limits retained. Own772historyrecords no protectedcomponents, no universalcompliance claim.',root_scope='Documentary integrity/routing only; no root mathematical solving/programs/Lean/checkers or protected externalpathfollow',credit=0,accepted_new=57,target_new=60,formal_dispatch=False,terminal_self_exclusions=exclusions)
save(P/'expanded-corpus-r471-parent-integration.json',record)
den=json.loads((ROOT/'inherited-denials-r473.json').read_text());den['utc']=now
den['blocked_keys']=sorted(set(den['blocked_keys'])|{urlsplit(unavailable['requested']).hostname.lower()+unquote(urlsplit(unavailable['requested']).path).rstrip('/')})
den['blocked_artifacts']=sorted(set(den['blocked_artifacts'])|{'srds03.pdf','epidemic spreading in real networks: an eigenvalue viewpoint'})
den['records'].append(dict(url=unavailable['requested'],reason=dict(status='HTTP200after302redirecttoauthorhomepage;nonPDFHTMLbody',artifact=unavailable['work'],restriction='ENTIREidentifiedWDWF2003work ALLnewalternatehosts/versions/arxiv/authors/caches/mirrors/DOI/API/body/metadata deliveryunavailable. No retry orindirect recovery; do not search/fetchalternativecopies orexpandedversiondelivery. Guardtransporthistoryunchanged, scientificclassification separate. This doesNOTdeny every distinct epidemic paper or the actualalreadyacquired1111.0531/2212.05733 works.'),evidence=dict(path=str(A/'new-unavailability.json'),sha256=sha(A/'new-unavailability.json'),payload=str(A/wdwf['destination']),payload_sha256=sha(A/wdwf['destination']),guard_sha256=sha(A/'guard-ledger.jsonl'))))
den['root_r471_scope']='322479authorP4ordinaryfullnegation sourceconflict actualTakigawa2212.05733Section4READ, newindependentreviewassigned; WDWF2003srds03.pdfredirectedhomepagenonpaper, entireworkALLnewdeliveryunavailable. No freshlookuprecovery/routineexclusionfromsnippet.321481/319771actualpublic0,319943/321731fullgaps,320173degeneratepairsnotwitness.145ownmanifest20originalbindings13frozenverified,11hops9transport8PDF2redirects,3search9queries,772ownaccessrecords no protectedcomponents.57/60unchanged.'
denpath=ROOT/'inherited-denials-r474.json';save(denpath,den)
assert not R.exists();R.mkdir();(R/'inputs').mkdir();base=P/'expanded-corpus-r433'
for name in ['bootstrap.py','run.py','write_lane.py','verify_frozen.py','registry-roots.json','source_get_guard.py','model-policy-sol-only.json']:shutil.copyfile(base/name,R/name)
shutil.copyfile(ROOT/'charge_search.py',R/'charge_search.py');shutil.copyfile(denpath,R/'inherited-denials.json')
raw=base64.b64decode(prov['322479']['raw_b64'],validate=True);literal=json.loads(raw);(R/'inputs/original322479.raw.jsonl').write_bytes(raw);save(R/'inputs/literal322479.json',literal);save(R/'inputs/author-gates322479.json',gates['322479'])
s=(A/'ORDINARY-DERIVATIONS.md').read_text();start=s.index('## 322479:');end=s.index('\n## 319943:',start);(R/'inputs/author-proof322479.md').write_text(s[start:end]+'\n')
for name in ['virus.pdf','virus.txt','takigawa.pdf','takigawa.txt']:shutil.copyfile(A/'sources'/name,R/'inputs'/name)
for name in ['get-virus.json','get-takigawa.json','new-unavailability.json']:shutil.copyfile(A/name,R/'inputs'/name)
shutil.copyfile(ROOT/'accepted57-review-context.json',R/'inputs/accepted57-scopes.json');prior=P/'spherical-error-monotonicity-source-review-sol-r1/inputs/prior39-routing.json';assert sha(prior)=='6493e29137d286242b09d96f97dfe39a9ca5146a8d73bcfa8177e4705d6aaff3';shutil.copyfile(prior,R/'inputs/prior39-scopes.json')
save(R/'reservation.json',dict(ids=[322479],rows=[literal],purpose='Independent ordinary/source/significance review; no formaltools or selfacceptance'));(R/'reservation.sha256').write_text(sha(R/'reservation.json')+'  reservation.json\n');save(R/'search-budget.json',dict(calls_used=0,queries_used=0,maximum_calls=2,maximum_queries=6,charged_before_call=True))
task=f'''GPT-6.1 Sol high effort/default speed ONLY. Independent full proof/source/significance review of MathDB322479 rationalP4 virus-dynamics fixedpoint refutation. No children/providerfallback/formaltools/selfcredit. Current57/60 beyond39 prior,96total. Root orchestrates; you personally do mathematics/source comparison.

FIRST shell command EXACTLY:
timeout 20 python3 -I -B {R}/bootstrap.py
Read COMPLETE TASK/AGENTS. SECOND EXACTLY:
timeout 140 python3 -I -B {R}/verify_frozen.py before
No trailing punctuation. Bootstrap and standalone before/after verifiers explicitcapexceptions, notunder run.py. ALLother substantive local operations use immutable ABSOLUTE {R}/run.py withfreshlabel/Pythonstdin; all ownwrites via immutable ABSOLUTE {R}/write_lane.py. Never rerun bootstrap/editfrozenhelpers/inputs/caps/TASK. Preserve realfailures, targetrepairs; ordinarylocaltypo/render/serialization notautomatically externalpolicybreach. Actualaccess/protectedfile/guard/counter/cap violation STOP/quarantine, preserveevidence/noreset.

Assigned sole322479. Protected active/planned peers expanded-corpus-r472 and lr-translation-degree-source-proof-review-sol-r1, no read/stat/hash/list/glob/poll evenmetadata. Historical access ONLY own frozen inputs/. NO authorlane/ROOT/campaign/historyfiles, noembeddedpathfollow, nooldcertificateaudit. Allformal/code-loop/Polynexus/crown/bunkbed/tournament/Hat bodies andflatbasenames protected despite oldallowlisting. r463/r466ALLoutputs/acquisitions/claimsquarantined,noreuse. This review has NO historicalallowlist. Trusted57+39 fullscope snapshots are boundedfamilycontext, notcertificates.

Read exactoriginalJSONL/literal and cachedactual1111.0531v2, itsmodel(1.7)/(5.1), Conj5.2, allstandinghypotheses, probability/parameterdomains, rootedtree/level/branching definitions, whetherni1isallowed andwhetherfixedpointsrangeoverallnodesorlevel-synchronizedcoordinates. Read cachedactual2212.05733v2 Section4/Theorem4.1 and actualeliminationproofs. These bodies are acquired, notunreadproofHOLDs. Inspect actualmaterialthreshold glyph/map/equation pages visually usingPDFskill /home/mj-kang/.codex/plugins/cache/openai-primary-runtime/pdf/26.1103.10131/skills/pdf/SKILL.md (announce/readskill). No PDFauthoring requested. No visual/source-final equivalence from extractedtext alone.

INDEPENDENTLY proveorbreak authorP4 certificate:ell4,n1=n2=n3=1,a1/2,b3/10, explicitfourcoordinatepolynomialmap over[0,1]^4. Auditalltree-to-map correspondence, symmetryassumptions, unionboundlinearmajorant, rationalweights(3,5,5,3), weightedfixedpointcontradiction, exactsqrt3thresholdcomparison, andnegation ofexistence/uniquenessiff. Absence ofANYnonzerofixedpointmustbeproved, notjustabsenceofsynchronizedones. IfP4fallsoutsideactualstandingrange, donot silentlychangehypotheses orclaim literalcorrectionasdiscovery; investigate a genuinelyadmissible exactmechanism iffeasible beforeparking. All-pathsecondaryargument/diagnosticgolden-ratio variant are onefamily, notextracredit. Author proof is not your independentPASS. No numerical tests/enumeration/experiments/mathprograms/CAS/solvers/Lean/compiler/checker/formalAPI. Documentary/PDFprocessing onlyunder caps.

Scientificsourceconflict: author saysTakigawa2022Theorem4.1IIaassertssamefalseexistence foractualdisplayedmap; checkthispreciselyincludingnodenumbers, parameterandboundaryconventions. Do NOTaccept acontradictoryclaimedtheorem justbecausepublished; exhibit exact conflict or exposewhichmap/hypothesisdiffers. Investigate actualfinal/current/corrections/originalintendedscopewithboundedprimaryevidence. No theoremfrommathematicalshortness alone. Strongest significancecase and strongestcountercase required. Fullcorrectconjecture-negation to laterclaimedtheorem canmatter, but an applicableoldgeneralnetworkextinction theorem maygivecomplete routineadaptation; payexactmodel/toparameter/witnessbridge ifsupported,notjustkeywordanalogy.

WDWF2003WangChakrabartiWangFaloutsos 'EpidemicSpreadinginRealNetworks:AnEigenvalueViewpoint' at cs.cmu.edu/~deepay/mywww/papers/srds03.pdf is ALREADYUNAVAILABLE: actualrequest302redirectedtoauthorhomepage200HTML, notpaper. EntireidentifiedworkALLNEWalternatehosts/versions/arxiv/authors/expandedversiondeliveries/caches/mirrors/DOI/API/body/metadata UNAVAILABLE. Do NOTretry, searchforalternativecopies, alterURLs/versions orindirectlyrecoverit. Frozennew-unavailabilityrecordsactualfailure,guardhistorynotrepaired. This is NOTablanketban on everydistinctepidemicpaper. You maycompareother genuinelydistinctprimaryworks withinbudgets, notuse them as a disguised deliveryofWDWF. Readactualcachedsourcecitations/claims; no matchingroutineprior proofinference fromacitationorhomepage. A specificallyapplicableunreadproof is preciseHOLD; genericworldwideunknown isnotautomaticveto. Ifa completeactualprimary-to-targetroutinebridge existsdocumentitandstrongestcontrarysignificancecase. Otherwise retainexactlimit, notunsupportedroutineexclusionorworldwidenoveltyclaim.

Compareboundedtrusted57+39 fullscopes. Sharedpath/star/spectral/epidemicvocabulary alone isnotfamilyidentity; actualmodel/endpointrelationship controls. Anyalreadycreditedfamilyscope cannotbe countedagain as allpaths/helper/oneparameter/formalizationvariant. ConditionalDORMANT-SOL-FORMAL-PLAN onlyiffullordinaryliteral/scientificgates survive; exactobjects/treecorrespondence/universalnegation/allbridges/allowedaxiomslisted. Noimplementation/formaldispatch,selfacceptanceorcredit.

Read ENTIRE inheriteddenials before network, recovermaterialtruncations. Sole GETclientimmutable source_get_guard.py underrun.py, ONE manuallyselected persistedexactplan perinvocation with url/routes/destination/source_identity/purpose, routes['322479'],unique new sources/destination,identity/purpose>=12chars. Max8GETHOPS TOTAL, redirects charged; max2native searches6exactquerystrings WHOLEreview. NocustomHTTP/requests/curl/wget/HEAD/nativeopen-fetch/browser/accounts/API/POST/TLS/cookie/JS/metarefreshworkarounds. EveryfailuremakesidentifiedworkunavailableacrossALLnewhosts/versions/arxiv/authors/caches/mirrors/DOI/API/body/metadata; noretry/alternateidentitycorrection/indirectrestore. Fourregistry-rootmetadataartifactsblocked,norefresh/reconstruction,notbanoneverydistinctprimary. Allotherinheritedworkspecificblocksretained.

BeforeEACHnative searchpersist exactqueries-listplan viawriter; chargeusingimmutable ABSOLUTEcharge_search.py underrun.py, LIVEcontinuity. Nevermanuallyedit/reset/refundsearch-budget.json/search-charges.jsonl. SaveFULLactualresponseimmediately. SupportedplainJSON/stringserialization, notbtoa/TextEncoder. PreserveserializationfailuresandsaveSAMEinmemoryresponsebeforefurtherresearch,withoutanothernetworkcall. Searchsnippetsnavigationnotproof. Onactualpolicy/budget/accessbreachSTOPnetwork/mathquarantinepreserve,noreset. NormalfailedGETworkunavailable notautomaticallypolicybreach.

Capsaffinity<=2,childCPU115/supervisor120,AS6GiB,sampledgroupRSS6GiB,deadline130/outer140,arena2. StandaloneverifierCPU120exception. Truereceipts/output/resources,synchronousreaping,no backgroundjobs. AllwritesOWNlane ONLY,no/tmp/parent/shared/dependencyedits/git/install/publish/accounts/messages. Native/transient/writerpeaksunknown,nouniversalcomplianceclaim.

Deliver REVIEW.md,independentPROOF.md orGAP.md,keyedreview.json322479withseparate literal/source/ordinary/prior/novelty/significance/family/formal/independent/procedure/acceptancegates,source-map,exactread/figure/access/search/resourceinventories,objections/strongestcontrarycases,actualreceipts/hashmanifest. Finalstandalonefrozen-after,thenactualbytemanifestincludingEVERYcompletedreceiptJSON/helpers/frozeninputs/plans/payloads/responses/guardledger/reports/frozen-after withpreciselynamedterminalnoncircularexclusions; no subsequentfrozenwrites. Completeactualboundedreview,notacknowledgment/acquisitiononly. OrdinaryPASSisnotrootacceptance;credit0,57/60unchangeduntilrootadjudication.
'''
(R/'TASK.txt').write_text(task);files=[q for q in R.iterdir() if q.is_file() and q.name!='search-budget.json']+list((R/'inputs').iterdir());save(R/'frozen-inputs.json',{str(q):sha(q) for q in files})
ready=dict(utc=now,lane=str(R),mathdb_id=322479,task_sha256=sha(R/'TASK.txt'),frozen_bindings=len(files),model='gpt-6.1-sol',reasoning='high',service='default',accepted_new=57,credit=0,protected_peers=['expanded-corpus-r472','lr-translation-degree-source-proof-review-sol-r1'],source_copy_scope='Cleanr471 target-only exactliteral/proof/actualoriginal+Takigawa bodies; no quarantinedinputs')
save(ROOT/'virus-path-review-r1-ready.json',ready);save(ROOT/'selection-routing-virus-path-review-r1.json',dict(ids=[322479],sources=['https://arxiv.org/abs/1111.0531','https://arxiv.org/abs/2212.05733'],task_sha256=ready['task_sha256'],lane=str(R),metadata_only=True))
save(ROOT/'lr-discovery-virus-prelaunch-addendum.json',dict(utc=now,immutable_existing_inputs_unchanged=True,protected_discovery472_peers=['lr-translation-degree-source-proof-review-sol-r1',R.name],protected_lr_review_peers=['expanded-corpus-r472',R.name],new_manual_unavailability={k:v for k,v in den['records'][-1].items() if k!='evidence'},scope='Dispatch-onlylateststeering,notpermissionfornewhistoricalpaths; olderfrozendenialsunchanged, manualwork-widefailurebindingbeforeeveryGET. NewP4reviewfreshsnapshotincludesallblocks.'))
print(json.dumps(dict(accepted_new=57,manifest_files=145,original_bindings=20,frozen_bindings=13,receipt_exit_counts=record['receipt_exit_counts'],new_unavailable_work=unavailable['work'],review=ready)))
