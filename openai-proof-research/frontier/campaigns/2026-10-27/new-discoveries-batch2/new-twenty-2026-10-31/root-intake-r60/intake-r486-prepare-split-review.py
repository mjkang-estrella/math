"""Root documentary integrity and target-only review construction; no mathematical execution."""
import os,resource
os.sched_setaffinity(0,sorted(os.sched_getaffinity(0))[:2]);resource.setrlimit(resource.RLIMIT_CPU,(120,120));resource.setrlimit(resource.RLIMIT_AS,(6*1024**3,6*1024**3))
from pathlib import Path
import json,hashlib,datetime,collections,re,shutil,base64
P=Path(__file__).resolve().parent.parent;ROOT=P/'root-intake-r60';A=P/'expanded-corpus-r486';R=P/'split-decomposition-orthogonality-source-review-sol-r1'
def sha(q):return hashlib.sha256(q.read_bytes()).hexdigest()
def dg(b):return hashlib.sha256(b).hexdigest()
def read(q):return json.loads(q.read_text())
def save(q,d):
 assert not q.exists(),str(q)
 q.write_text(json.dumps(d,indent=2)+'\n')
now=datetime.datetime.now(datetime.timezone.utc).isoformat();assert read(P/'ledger.json')['accepted_new']==57
route=read(ROOT/'selection-routing-r486.json');assert sha(A/'TASK.txt')==route['task_sha256'] and sha(A/'reservation.json')==route['reservation_sha256']
m=read(A/'SHA256-MANIFEST.json');entries={x['path']:x for x in m['files']};assert len(entries)==len(m['files'])==164
for n,v in entries.items():
 assert not Path(n).is_absolute() and '..' not in Path(n).parts
 q=A/n;assert not q.is_symlink() and sha(q)==v['sha256'] and q.stat().st_size==v['bytes'],n
ex=m['terminal_noncircular_self_exclusions'];assert set(ex)=={'SHA256-MANIFEST.json','terminal_manifest.receipt.json','terminal_manifest.output.txt'}
actual=set()
for q in A.rglob('*'):
 assert not q.is_symlink()
 if q.is_file():actual.add(str(q.relative_to(A)))
assert actual==set(entries)|set(ex)
frozen=read(A/'frozen-inputs.json');assert len(frozen)==13 and all(Path(n).parent==A and sha(Path(n))==h for n,h in frozen.items())
after=read(A/'frozen-after.json');before=read(A/'frozen-before.json');assert before['count']==after['count']==13 and before['mismatches']==after['mismatches']==[]
gates=read(A/'results.json');literals=read(A/'literals.json');ids=read(A/'reservation.json')['ids'];assert len(ids)==20 and set(ids)==set(map(int,gates))==set(map(int,literals))
chunks={};sources={};provenance={}
for number in ids:
 key=str(number);row=read(A/'originals'/f'{key}.json');q=Path(row['chunk']);assert q.is_relative_to(P.parent/'lanes/pi-mathdb-full-corpus-inventory-r301/corpus')
 if str(q) not in chunks:
  b=q.read_bytes();chunks[str(q)]=(dg(b),b.splitlines(keepends=True))
 h,lines=chunks[str(q)];assert h==row['chunk_sha256'];raw=lines[row['line']-1];obj=json.loads(raw)
 assert row['newline'] is True and raw.endswith(b'\n') and dg(raw)==row['raw_sha256'] and base64.b64decode(row['raw_base64'],validate=True)==raw and (A/'originals'/f'{key}.raw.jsonl').read_bytes()==raw
 assert obj==literals[key] and obj['mathdb_id']==number
 tokens=re.findall(rb'"statement"\s*:\s*("(?:[^"\\]|\\.)*")',raw);assert len(tokens)==1;token=tokens[0]
 assert token.decode()==row['statement_token'] and dg(token)==row['statement_token_sha256'] and json.loads(token)==row['statement']==obj['statement'] and dg(obj['statement'].encode())==row['statement_sha256']
 sources[key]=obj['source_url'];provenance[key]=row
receipts=[]
for q in sorted(A.glob('*.receipt.json')):
 v=read(q);assert v['cwd']==str(A) and v['cpu_limit_s']==115 and v['as_limit_bytes']==6*1024**3 and v['deadline_s']==130 and len(v['affinity'])<=2 and v['group_rss_guard_bytes']==6*1024**3 and v['killed'] is None
 receipts.append(dict(path=q.name,sha256=sha(q),exit=v['exit']))
assert read(A/'terminal_manifest.receipt.json')['exit']==0
budget=read(A/'search-budget.json');assert budget==dict(calls_used=3,queries_used=9,maximum_calls=3,maximum_queries=9,charged_before_call=True)
charges=[json.loads(s) for s in (A/'search-charges.jsonl').read_text().splitlines()];assert len(charges)==3
prev=dict(calls_used=0,queries_used=0,maximum_calls=3,maximum_queries=9,charged_before_call=True)
for word,c in zip(['one','two','three'],charges):
 assert c['sequence']==prev['calls_used']+1 and c['before']==prev and sha(A/c['plan'])==c['plan_sha256'] and read(A/c['plan'])['queries']==c['queries']
 nxt=dict(prev,calls_used=prev['calls_used']+1,queries_used=prev['queries_used']+len(c['queries']));assert c['after']==nxt;prev=nxt
 response=read(A/f'search-{word}-response.json');assert isinstance(response,str) and len(response)>1000
assert prev==budget and sha(A/'charge_search.py')==sha(ROOT/'charge_search.py')
events=[];prev='0'*64
plans={dg(json.dumps(read(q),sort_keys=True).encode()):read(q) for q in (A/'plans').glob('*.json') if 'url' in read(q)}
for i,line in enumerate((A/'guard-ledger.jsonl').read_bytes().splitlines(keepends=True)):
 e=json.loads(line);assert e['seq']==i and e['previous']==prev;prev=dg(line);events.append(e)
 if e['event']=='success':assert sha(A/e['destination'])==e['sha256'] and (A/e['destination']).stat().st_size==e['bytes'] and (A/e['destination']).read_bytes().startswith(b'%PDF')
 if e['event']=='attempt':assert e['plan_sha256'] in plans and '/server/api/' not in e['url']
counts=collections.Counter(e['event'] for e in events);assert counts==dict(attempt=9,success=9)
history=read(A/'history-access.json');allow=read(A/'historical-results-allowlist.json');assert len(history)==808
forbidden=('formal','code-loop','code_loop','polynexus','crown','bunkbed','tournament','hat-bipartite')
for x in history:
 rel=Path(x['path']).relative_to(P)
 assert not any(t in part.lower() for part in rel.parts for t in forbidden)
 assert not any(f'expanded-corpus-r{n}' in x['path'] for n in [395,463,466,482])
 assert x['path'] in allow and allow[x['path']]==x['sha256']
summary='382572authorfullsource-dependentorthogonalityargumentusesactualAssumption8.1,Section7orthogonalTmodules,Lemmas10.3/11.3/11.4 andglobaldirectsum-equalitybridge;routineadaptationproposalbutexplicitConj13.6contrarycase,independentfidelity/proof/significanceunpaid,assignedreview. Skolem336611/379053/379055necessity/sourcepermutationbijection/saturatedboundaryreductionpaid,strictunsaturatedrealizationandall-diagonalintegralmatchingunpaid.355158sourceprobabilitynormalizationcorrection0,intendedterminating3F2excessminus1identityunpaid,ordinarySaalschutz/interswitch/interpolationnotproof.380003actualBassinoBouvelRossinTh5.1pin-wordrationalitypublic0,classification/figuresattributednotindependentlyaudited.379035actualMatsushitachi2retractionpublicproof0.379199actualChebotarev2610.14100v3Lemmas7-8Th9analyticpublicrefutation0,notnewdecimalcertificate.380116unsignedsign/379340edgecliqueinvariant-Oreconflationcorrections0,intendedcorrectedfullquestionsunpaid.'
record=dict(utc=now,source_lane=str(A),task_reservation_genesis_verified=True,manifest_sha256=sha(A/'SHA256-MANIFEST.json'),verified_manifest_files=164,verified_original_bindings=sorted(ids),verified_frozen_bindings=13,source_url_by_id=sources,all20_gates=gates,runner_receipts=receipts,receipt_exit_counts=dict(collections.Counter(str(x['exit']) for x in receipts)),guard_events=dict(counts),search_budget=budget,root_disposition='ZERO_QUALIFIED_SURVIVORS_382572_ASSIGNED_INDEPENDENT_REVIEW',scientific_summary=summary,reading_limits='Fourteenexactassignedoriginalbodiesunread;matchingfollowups/2005predecessornotoriginal/finalequivalence. Pinclassification/diagrams anddeeptridiagonal/analyticinputsattributed,nofreshindependentaudit. No visualinspection claimed.',process='808savedhistorynamesandownsavedallowlisthashescomparedwithoutfollowingexternalpaths;164ownfiles20corpusraw/token/decodedbindings13frozen9PDFGETsuccess3search9queriesverified. New316244restrictionsteeringsaved,frozenunchanged. Actualsamplesonly,native/transient/writer/supervisorpeaksunknown,nouniversalcomplianceclaim.',root_scope='Documentaryprovenance/integrity/routingonly,no root mathematical solving/programs/Lean/checkers.',credit=0,accepted_new=57,target_new=60,formal_dispatch=False,terminal_self_exclusions=ex)
delta='Completedr486zeroqualifiedsurvivors. '+summary+'164ownfiles20bindings13frozen808savedhistorypathsverified,9PDFGETsuccess3search9queries,nonewdenials/dispatch/credit.57/60unchanged.'
den=read(ROOT/'inherited-denials-r491.json');den['utc']=now;den['root_r486_scope']=delta;denpath=ROOT/'inherited-denials-r492.json'
# Verification is complete before root-only integrations and fresh review preparation.
save(P/'expanded-corpus-r486-parent-integration.json',record);save(denpath,den)
assert not R.exists();R.mkdir();(R/'inputs').mkdir();base=P/'expanded-corpus-r433'
for name in ['bootstrap.py','run.py','write_lane.py','verify_frozen.py','registry-roots.json','source_get_guard.py','model-policy-sol-only.json']:shutil.copyfile(base/name,R/name)
shutil.copyfile(ROOT/'charge_search.py',R/'charge_search.py');shutil.copyfile(denpath,R/'inherited-denials.json')
literal=literals['382572'];shutil.copyfile(A/'originals/382572.raw.jsonl',R/'inputs/original382572.raw.jsonl');shutil.copyfile(A/'originals/382572.json',R/'inputs/provenance382572.json');save(R/'inputs/literal382572.json',literal);save(R/'inputs/author-gates382572.json',gates['382572'])
author=(A/'ORDINARY-INVESTIGATION.md').read_text();target=author[author.index('## 382572:'):author.index('\n## 336611,')];(R/'inputs/author-proof382572.md').write_text(target+'\n')
for name in ['FULLCANDIDATE.md','DORMANT-SOL-FORMAL-PLAN.md']:shutil.copyfile(A/name,R/'inputs'/name)
for name in ['split.pdf','split.txt','displacement.pdf','displacement.txt']:shutil.copyfile(A/'sources'/name,R/'inputs'/name)
for name in ['split.json','displacement.json']:shutil.copyfile(A/'plans'/name,R/'inputs'/('get-'+name))
shutil.copyfile(ROOT/'accepted57-review-context.json',R/'inputs/accepted57-scopes.json');prior=P/'spherical-error-monotonicity-source-review-sol-r1/inputs/prior39-routing.json';assert sha(prior)=='6493e29137d286242b09d96f97dfe39a9ca5146a8d73bcfa8177e4705d6aaff3';shutil.copyfile(prior,R/'inputs/prior39-scopes.json')
save(R/'reservation.json',dict(ids=[382572],rows=[literal],purpose='Independentfullsource-splitorthogonalityproofandconcretesource-prioradaptationqualification,noformaltools/selfacceptance'));(R/'reservation.sha256').write_text(sha(R/'reservation.json')+'  reservation.json\n');save(R/'search-budget.json',dict(calls_used=0,queries_used=0,maximum_calls=2,maximum_queries=6,charged_before_call=True))
task=f'''Use ONLY GPT-6.1 Sol, high effort, default speed. Personally and independently review MathDB382572 full source-bound four-split orthogonality theorem, literal fidelity, ordinary proof, source/prior subsumption and significance. Current57/60 beyond39 prior,96total. No children/fallback, mathematical programs or formal tools. Root orchestrates; you do mathematics. Complete the bounded review, not an acknowledgment or acquisition-only handback.

FIRST shell command EXACTLY:
timeout 20 python3 -I -B {R}/bootstrap.py
Read COMPLETE printedTASK/AGENTS. SECOND EXACTLY:
timeout 140 python3 -I -B {R}/verify_frozen.py before
No punctuation/chaining. These standalone bootstrap/verifiers are explicit cap exceptions. Every other substantive local operation immutable ABSOLUTE {R}/run.py UNIQUE_LABEL Python stdin; authored writes immutable ABSOLUTE {R}/write_lane.py. Preserve failures/targetedrepairs with freshlabels; never rerun bootstrap or edit frozen helpers/inputs/TASK/caps. Actual protected/frozen/access/guard/counter/cap breach STOP/quarantine/no reset. Ordinary documentary typo/render/serialization failures are not automatically policy breaches.

SOLE382572. Protected active peers expanded-corpus-r485 and expanded-corpus-r487,evenmetadata/stat/read/hash/list/glob/poll/reservations/flat integrations. NO history allowlist. Read only ownfrozeninputs/products and explicitPDFskill,not authorlane/ROOT/campaign/history/embeddedpaths. ALL formal/code-loop/Polynexus/crown/bunkbed/tournament/Hat bodies andflat integration basenames protected. ALL r395/r463/r466/r482 packets permanently quarantined,no reuse/refetchseeds. Public /server/api/.../content is forbiddenAPI despitePDF-lookingdelivery/guardtransport200. All writes soleownlane,no/tmp/shared/parent/git/install/publish/accounts/messages. Trusted57+39 scopes onlyboundedcontext,no upstreamcertificateaudits.

Read exact raw/literal and actual supplied math0608694v1 source,not arbitrary flags. Independently reconstruct precise standing Assumption8.1/Remark8.2,finite distance-regular graph and classical parameters (D,b,b-1,beta),b!=1,primitive-idempotent ordering,standardcomplexHermitianform,T algebra/irreduciblemodules,source endpoint/dualendpoint/diameter ranges. ReadSection7,Definitions10.1-10.4,Lemmas10.3/11.2-11.5 with proofs,Conjecture13.6 and relevant context. Distinguish orthogonal complement defining actual tilde spaces from arbitrary chosen direct complements. Recover all r,s indexquantifiers/cross-orientations/zero spaces/sourceparameters; generic universal-pair-of-flags theorem is not this conjecture and is unsafe. Identify any corpus/source corrections explicitly,zero credit,not a replacement theorem.

Before relying on author proof, sustain YOUR full ordinary route from actual source definitions/primary statements. Then adversarially audit inputs/author-proof382572.md. Author uses an orthogonal decomposition V=sum W,4eigenspace decompositions Lemma11.3,4global index placements Lemma11.4,globaldirectsum10.3,and spectral-support orthogonality. Crucial unpaid-to-review bridge: global tilde space is EXACT sum of actual Wpieces with matchingglobalindices,not just each Wpiece included. Verify why regrouping/directsumuniqueness pays this,why Wprojections then stay in appropriateflags/tildepieces,why every Wpiece is included at allowedindices,and why cross-W terms vanish. Check both DD/UU and DU/UD equations for ALLindices,zero/outofrange cases,without thinness/rho=tau/realq/newhypotheses. Require genuine zero innerproduct for whole spaces,not just orthogonality of selectedeigenvectors or matching indexsum. If proof fails, repair concretely or exactGAP,do not silently weaken endpoint.

Actual2005 companion math0306142 Lemma6.1 proof is supplied separately. Read applicable actualtheorem/proof and map it to2006Lemma11.4 instead of treating citation as inspectedtruth. Deeper tridiagonal/q-tetrahedron/semisimplicity inputs may be cited with exacthypotheses and candid imported-proof limits; this ordinary review is not a fresh foundational proofaudit. If source glyph/definition/table/diagram materially matters,use/announce/read explicit PDFskill /home/mj-kang/.codex/plugins/cache/openai-primary-runtime/pdf/26.1103.10131/skills/pdf/SKILL.md and visually inspect actual renderedpages locally. NoPDFauthoring,installs or otherlane paths.

Scientificgate: author's proposed complete routineadaptation from SAME source Section7/Lemmas10.3/11.3/11.4 is a recommendation,not rootadjudication. Strongest positivecase: exact source expressly prints fullConj13.6 and actualmodule-to-globalorthogonality may supply missing substantivecontent. Strongest contrarycase: fulltarget follows by directsumuniqueness and support arithmetic appliedtoalready-provedsource decompositions. Judge actual complete primary-to-targetbridge,not shortness/standardtool use or source openlabel. If routineexclude,write COMPLETE bridge and assumptions,do not claim earlier exactprintedcorollary withoutreadingit. If substantive,explain precisely what originallemma is new/why general prior doesn'tsubsume. No generic worldwide-unknown veto; specific relevant unreadproof is preciseHOLD, boundednonmatchesnotnovelty.

Bounded current/final/prior comparison,actualprimarybodies notsearchsnippets. Author identified a relevant Kim2009 paper on thesematrices but body UNREAD; first authenticate exactidentity/scope then actualtheorem/proofif available. Do not conflate neighboring Conj13.9,arbitrarytridiagonalpair flags,formalselfduality or a latermatrixresultwiththisexact two-orientationorthogonality. Current final/correction status of original work unqualified; nofinalabsenceinferredfromcachedarxiv. Read complete applicable companionproof rather than abstract. Four registryrootmetadataartifacts remain unavailable,no refresh/reconstruction viaREADME/tree/API/branch/version. Distinctprimarypapers notblanketdenied. Compare supplied57+39 fullscopes only; sharedgraph/orthogonality/linearalgebra notautomatically duplicate. Allorientation/parameter/helper variants onefamily,public/routine/source/domaincorrection/formalization outcomeszero.

No mathematicalprograms/enumeration/numericaltests/experiments/CAS/solver/Lean/compiler/checker/formalAPI. Personal ordinary reasoning only; documentary/hash/source/PDFprocessing allowed. No costlyformalplanif routine/publicexclusion/fidelityGAP. Conditional dormantSolbrief onlyif full literalordinaryandscientificgates survive; exactgraph/association/Talgebra/spectralflags/tildeorthocomplement/module/globalbridge/literalendpoint dependencies,permittedaxioms only. Noimplementation/dispatch/selfacceptance.

Network: read ENTIRE inherited-denials,recovermaterialtruncations BEFORErequests. SoleGET immutable source_get_guard.py UNDERrun.py. ONE manuallyselected exactpersistedplan/invocation,url/routes/destination/source_identity/purpose,route['382572'],NEWown sourcesdestination,identity/purpose>=12chars. Max8GET HOPS total,redirectscharged. Max2 nativeSEARCH calls6exactquerystrings. BeforeEACHsearch persist exactquerieslistplan viawriter,readLIVEcounter/ledger,prechargeimmutableABSOLUTEcharge_search.py underrunner;nevermanualreset/refund/editcounters/ledger. Save FULLactualresponse immediatelybeforeotherwork,ordinaryJSON/stringserialization,no btoa/TextEncoder; recoverSAMEinmemoryresponsewithoutanothercall onlocalserializationerror. Searchsnippetsnavigationnotproof.
NoAPI includingpublicrepository/server/api bitstreams,customHTTP/curl/wget/requests/HEAD/nativeopenfetch/browser/accounts/POST/TLS/cookie/JS/meta-refresh workaround. Everyfailureidentifiedwork ALLNEW hosts/versions/arxiv/authors/caches/mirrors/DOI/API/body/metadata unavailable,no retry/identitycorrection/indirectrecovery. Guardhistoryunchanged; transport200nonpaperscientificclassificationseparate. Inherited0704.0541/JCTAfinal,1106.5068/LAAfinal,and2014Poly-antimatroidpolyhedra work blocks plusALLolderrestrictionsbinding; explicit cachedpredenialcopiesonly,noalternate. A guard-preventedrepeatredirect is not a performedrefetch butSTOP/reportpreserved,noreset. Do not recover unavailableworks indirectlythroughdistinctmetadata. Distinct actual otherworknotblanketdenied.

Caps affinity<=2,childCPU115/supervisor120,AS6GiB,sampledgroupRSS6GiB,deadline130/outer140,arena2. Allsynchronous runnerreceipts withactualresources/reaping,no backgroundjobs. StandaloneverifierCPU120exception notnestedunderchild115. Native/transient/writer/supervisorpeaksunknown,no universalcomplianceclaim.

Deliver REVIEW.md,independent PROOF.md orpreciseGAP.md,keyedreview.json382572 separateliteral/source/ordinary/prior/novelty/significance/family/formal/independent/procedure/acceptancegates,actualsource-map,strongestopposingcases,read/visual/access/search/resourceinventories,actualreceiptsandSHAmanifest. Fullordinaryreview mustbecompletedorprecisegapreported. Final standalonefrozen-after THENmanifest EVERY ownfile/helpers/frozeninputs/plans/payloads/fullresponses/ledgers/ALLcompletedreceiptJSON,preciselynamedterminalnoncircularexclusions,no laterfrozenwrites. Credit0,57/60unchangeduntilrootacceptance.
'''
(R/'TASK.txt').write_text(task);files=[q for q in R.iterdir() if q.is_file() and q.name!='search-budget.json']+list((R/'inputs').iterdir());save(R/'frozen-inputs.json',{str(q):sha(q) for q in files})
ready=dict(utc=now,lane=str(R),mathdb_id=382572,task_sha256=sha(R/'TASK.txt'),frozen_bindings=len(files),model='gpt-6.1-sol',reasoning='high',service='default',accepted_new=57,credit=0,protected_peers=['expanded-corpus-r485','expanded-corpus-r487'],source_copy_scope='Cleanr486target-onlyliteral/provenance/authorargument/cachedactualsourceand2005companion/57+39scopes,noquarantine')
save(ROOT/'split-orthogonality-review-r1-ready.json',ready);save(ROOT/'selection-routing-split-orthogonality-review-r1.json',dict(ids=[382572],sources=[literal['source_url'],'https://arxiv.org/abs/math/0306142'],lane=str(R),task_sha256=ready['task_sha256'],metadata_only=True));save(ROOT/'r486-completion-boundary-delta.json',dict(utc=now,message=delta,new_protected_peer=R.name,immutable_worker_inputs_unchanged=True))
print(json.dumps(dict(manifest_files=164,frozen_bindings=13,original_bindings=20,receipt_exit_counts=record['receipt_exit_counts'],review=ready)))
