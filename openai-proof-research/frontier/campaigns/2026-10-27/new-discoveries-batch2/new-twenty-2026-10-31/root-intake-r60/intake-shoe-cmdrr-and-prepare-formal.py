import os,resource
os.sched_setaffinity(0,sorted(os.sched_getaffinity(0))[:2])
resource.setrlimit(resource.RLIMIT_CPU,(120,120))
resource.setrlimit(resource.RLIMIT_AS,(6*1024**3,6*1024**3))
from pathlib import Path
import hashlib,json,datetime,collections,shutil
P=Path(__file__).resolve().parent.parent;ROOT=P/'root-intake-r60'
S=P/'shoe-pair-discrepancy-source-review-sol-r1';C=P/'cmdrr-five-three-formal-sol-r2'
BASE=P/'flat-balance-bridges-formal-pi-r5'
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def save(p,v):
 assert not p.exists(),str(p)
 p.parent.mkdir(parents=True,exist_ok=True);p.write_text(json.dumps(v,indent=2)+'\n')
now=datetime.datetime.now(datetime.timezone.utc).isoformat()
assert json.loads((P/'ledger.json').read_text())['accepted_new']==55
intakes=[]
for lane,target in [(S,324571),(C,326555)]:
 manifest=json.loads((lane/'SHA256-MANIFEST.json').read_text())
 rows=manifest.get('files')
 if rows is None:rows=[{'path':n,'sha256':s} for n,s in manifest['sha256'].items()]
 assert all(sha(lane/x['path'])==x['sha256'] for x in rows)
 frozen=json.loads((lane/'frozen-inputs.json').read_text());assert all(sha(Path(s))==v for s,v in frozen.items())
 after=json.loads((lane/'frozen-after.json').read_text());assert not after['mismatches'] and after['count']==len(frozen)
 if lane==S: exclusions=list(manifest['terminal_self_exclusions'])
 else:exclusions=manifest['exact_self_exclusions']
 rec=[]
 for row in rows:
  if row['path'].endswith('.receipt.json') or row['path'].startswith('receipt/') and row['path'].endswith('.json'):
   v=json.loads((lane/row['path']).read_text());rec.append({'path':row['path'],'sha256':row['sha256'],'exit':v.get('exit'),'guard':v.get('guard',v.get('killed')),'group_members_left':v.get('group_members_left')})
 for n in exclusions:
  if n.endswith('.receipt.json') or n.startswith('receipt/') and n.endswith('.json'):
   v=json.loads((lane/n).read_text());rec.append({'path':n,'sha256':sha(lane/n),'exit':v.get('exit'),'guard':v.get('guard',v.get('killed')),'group_members_left':v.get('group_members_left'),'terminal_excluded_from_manifest':True})
 obj={'utc':now,'mathdb_id':target,'lane':str(lane),'manifest_sha256':sha(lane/'SHA256-MANIFEST.json'),'manifest_files_verified':len(rows),'manifest_mismatches':[],'frozen_count':len(frozen),'frozen_mismatches':[],'frozen_after':after,'terminal_self_exclusions':exclusions,'receipt_count':len(rec),'receipt_exit_counts':dict(collections.Counter(str(x['exit']) for x in rec)),'receipts':rec,'credit':0,'accepted_new':55,'target_new':60,'previous_accepted':39,'root_execution':'Documentary integrity/orchestration only; no mathematical program or Lean/checker execution'}
 if lane==S:
  prev='0'*64;events=[]
  for i,line in enumerate((S/'guard-ledger.jsonl').read_bytes().splitlines(keepends=True)):
   e=json.loads(line);assert e['seq']==i and e['previous']==prev;prev=hashlib.sha256(line).hexdigest();events.append(e)
   if e['event']=='success':assert sha(S/e['destination'])==e['sha256']
  assert sum(e['event']=='attempt' for e in events)==2
  obj.update({'review_sha256':sha(S/'REVIEW.md'),'proof_sha256':sha(S/'INDEPENDENT-PROOF.md'),'guard_chain_verified':True,'guard_last_sha256':prev,'guard_events':events,'independent_gates':json.loads((S/'keyedreview.json').read_text()),'root_status':'PROSPECTIVELY_QUALIFIED_FOR_FULL_LITERAL_LEAN_ONLY','root_adjudication':'Adopt independent ordinary/literal/original/final PASS, supplied94scope nonoverlap and substantive-content candidate PASS. Bounded actual1311.4243 theorem/proof nonmatch paid; no identified marked-color/strict-alternation theorem with needed conclusion left unread. Galbraith-Holmes2012body404 remains an explicit prior-access limit, not a proved applicable subsumer or generic veto. No worldwide novelty claim. Full formal pipeline and independent final review/root acceptance unpaid.','procedure':'Preserve failed renderer/import and404 receipts, orchestration-only btoa error before shell, recovered material truncation, native/writer/sampling limits; no universal compliance claim.','authorized_next':'Fresh GPT-6.1 Sol high/default implementation of ALL countably-supported probability/stopping/PMF/TV/supremum source bridges, audits, clean replay, controls and paper; no network/children/credit.'})
  output=P/'shoe-pair-discrepancy-source-parent-integration-sol-r1.json'
 else:
  state=json.loads((C/'results/326555.json').read_text());assert not state['endpoint_present']
  for mod in state['production_modules']:
   assert sha(C/'src'/f'{mod}.lean')==state['source_hashes_after_checker'][mod]
  for name,info in state['latest_real_exits'].items():
   q=C/info['path'];v=json.loads(q.read_text());assert sha(q)==info['sha256'] and v['exit']==info['exit']==0 and v['group_members_left']==[]
   if v.get('source'):assert sha(Path(v['source']))==v['source_sha256']
   if v.get('target_olean'):assert sha(Path(v['target_olean']))==v['target_olean_sha256']
   if v.get('log'):assert sha(Path(v['log']))==v['log_sha256']
  replay=json.loads((C/'results/PARTIAL-REPLAY.json').read_text());assert all(x['exit']==0 for x in replay['commands'])
  obj.update({'actual_state':state,'replay':replay,'root_status':'VERIFIED_PARTIAL_NOT_ACCEPTED','root_disposition':'Continue full literal theorem from ten source-only baseline modules; no acceptance or helper credit. Author229declaration transitive axiom audit and partial source-only replay are partial evidence only, complete body DAG/endpoint/controls/paper still unpaid.','process_deviations':state['process_deviations'],'prior_limit':'Unread2013companion403 retained; no network authorized','root_preparation_exception':'One earlier root manifest-schema reader KeyError before discovering this manifest uses sha256 mapping; no files changed by that failed read. This integrity pass handles the actual schema.'})
  output=P/'cmdrr-five-three-formal-parent-integration-sol-r2.json'
 save(output,obj);intakes.append({'lane':str(lane),'manifest_count':len(rows),'frozen':len(frozen),'receipts':len(rec),'exit_counts':obj['receipt_exit_counts'],'integration':str(output)})

old=ROOT/'inherited-denials-cover-mis-review-r1.json';den=json.loads(old.read_text());den['utc']=now
url='https://www.math.auckland.ac.nz/~sgal018/birthday.pdf'
den['blocked_keys']=sorted(set(den['blocked_keys']+['www.math.auckland.ac.nz/~sgal018/birthday.pdf']))
den['blocked_artifacts']=sorted(set(den['blocked_artifacts']+['galbraith-holmes2012 a non-uniform birthday problem with applications to discrete logarithms']))
den['records'].append({'url':url,'reason':{'status':404,'artifact':'Galbraith-Holmes2012 A non-uniform birthday problem with applications to discrete logarithms, Discrete Applied Mathematics160,1547-1560','body_obtained':False},'evidence':{'path':str(S/'guard-ledger.jsonl'),'sha256':sha(S/'guard-ledger.jsonl')}})
den['root_galbraith_holmes_scope']='Identified Galbraith-Holmes2012 non-uniform birthday paper unavailable across all alternatehosts/query/version/DOI/arxiv/author/mirror/cache/bodydeliveries after404. No retry. No specific marked-collision strict-alternation theorem with required color-law conclusion was identified; preserve concrete access limitation without claiming applicable prior theorem or worldwide novelty. Distinct acquired1311.4243v5 is not denied; no indirect recovery of denied body.'
denpath=ROOT/'inherited-denials-shoe-review-r1.json';save(denpath,den)

COMMON='''You personally are GPT-6.1 Sol high/default ONLY. No children/model/provider fallback. Full literal Lean research, not a helper-only task. Root orchestrates and does no mathematics/compiler execution. Current55/60 beyond39prior; no acceptance or credit here. No network/search/browser/curl/wget/HTTP, git, installs, accounts/messages, shared/parent/author writes, /tmp artifacts or background jobs. Work OWN lane only. Every other campaign lane/body protected except EXACT provenance paths hashed only by mandatory frozen verifier; embedded paths are not research-read authorization. Read OWN COPIED inputs and supplied immutable helpers plus pinned mathlib/core API only. Source/prior access limits preserved; no worldwide novelty claim.
FIRST command EXACTLY `timeout 20 python3 -I -B LANE/bootstrap.py`; read full TASK/ancestorAGENTS, preserve initial receipt. SECOND command `timeout 140 python3 -I -B LANE/verify_frozen.py before`. No prior math/source/API reads. Then read copied literal, independent ordinary proof/review, original/final source definitions and full checkpoint/rootintegration/pins in bounded split outputs; recover material truncations. Verify actual toolchain/hash/mathlibpin metadata under OWNrunner, no git. No new broad API reconnaissance/probes before first actual new-proof write+strict check. Later diagnostic-guided API inspection allowed, targetimports over fullMathlib memory overhead. No mathematical Python/numerical experiments, enumeration, external solver or CAS; actual Lean proofs/tactics only. No sorry/admit/added axioms/unsafe/partial/native_decide/extern/implementedBy. Do not encode conclusion or unpaid bridge as a structure field/hypothesis. Source semantics and universal endpoint fully proved, not conditional or finite-only proxy.

Every substantive read/API/compiler/audit/render via OWN immutable runner; use `source LANE/env.sh` then `timeout 140 python3 -I -B LANE/runner.py UNIQUE_LABEL -- COMMAND ARGS`. Wrappers already sourceenv: use **bash** LANE/check.sh MODULE and **bash** LANE/checker.sh MODULE to avoid permission126. Strict Lean4.34.1 -j1 -M3500 -DwarningAsError=true, ownbuild+upstreamONLY. Module-name checker with pinnedbinonPATH. True exits/full logs/receipts every attempt; no tailpipeline or unchangedfailed rerun. All file authoring via python3-I-B write_lane.py RELATIVE_PATH consuming TEXT stdin; never empty Lean payload/binary or --base64 to textwriter. Own binaries/rendering via documented capped generators. Preserve failed commands honestly. Avoid direct cat/sed log reads outside runner: emit bounded saved log excerpts through ownrunner. Shell variables must be actually initialized in same shell; no unbound PACKAGES_ROOT. Immutable PINS.json/frozen/helpers may NEVER be overwritten, even with generated build/extraction plans: use distinct filenames. Allcaps2cores CPU120/AS12GiB, sampledgroupRSS6GiB, devguard130/wall140,arena2, ownTMPDIR/cache. Allgroupsreaped; samplimits notperfectcgroupclaim.

Checkpoint every strict-green module with actual source/olean/log/receipt hashes, exact paid/unpaid boundary and latesttrueexit. Continue through FULL endpoint rather than voluntarily ending at a helper milestone; if interrupted partial handback must state exact unpaid lemmas without claiming complete. Only actual deep checks count. BeforetechnicalPASS: strict+leanchecker every production module; wholeenvironment enumeration inclprivate/generated/transitive body-origin DAG with actual per-endpoint closures and axiom union. Allowed propext/Classical.choice/Quot.sound ONLY, no imported unsupported theorem/trusted conclusion. Generic definition/source bridges must participate in endpoint chain. Substantive positive/nonvacuitycontrols and intentional semantic-mutation negativecontrols with true expectedfail logs. Fresh source-only extraction from EMPTYbuild, ownsourcehash equality, upstreamONLY path noold author/legacyoleans, strictall+checkerall; rehash AFTERchecker. No copiedoleans count as replay. All controls/auditsreceipts preserved, honest scope.

Complete readable paper with exact source/literal/theorem/proof/audit/replay and retained prior/process limits. PDFskillread via runner explicitlyallowed; announce use and execute required authoringmarker exactlyONCE for plannedPDF, availablegroff/reportlabwithoutinstall. OutputPDFunderoutput/pdf; render and actually inspect EVERYpage. Directdisplay of OWNrendered/documentaryimages allowed as distinctUIevidence; don't invent unavailabletool process telemetry. No wholebody/figureclaim from failedOCR. Final results/ID.json credit0,campaign55/60, SUMMARY/CHECKPOINT, fullsource-to-definition map, inventory of allcompleted receiptJSONs/helpers/inputs/pins/plans/sources/oleans/logs/audits/paper/renders/extractedbuild. ActualSHAmanifest with EXACTterminalnoncircularselfexclusions, notvaguefilenamepatterns. Mandatory standaloneverify_frozen after and no laterfrozenwrites. No ledger edits/selfacceptance. Independentfullfinal source-to-Lean/proof/deepbody/manuscriptreview and rootacceptance remain separate/unpaid. Handback ACTUALdiskstate only, alljobsreaped.
'''
SHOE='''FULL MathDB324571: sup over all discrete laws p of D(p,p)<1 under actual STRICTalternation. Rootprospectivequalification in inputs/ROOT-INTEGRATION.json, ordinary/literal/original/finalPASS,94scopeboundednonmatch, actual1311.4243proofnonmatch, Galbraith-Holmes2012body404unreadlimit. No retrieval or claim of globalnovelty. Source original1211.6486v2 Sections2-4/9, finalAAP47(2015)292-305 DOI10.1239/aap/1427814592 Sections9.1/9.2 equation19 Conjecture4, not5. Do not change to simultaneous pairs, randomarrivaltype, independentPoissonclocks, finitefixedsupport or abstract assumed minorization. CurrentMathDBchallengebody notclearance; immutableliteralprovided.

After mandatory reads/pinverification, FIRSTNEWPROOFoperation WRITE src/ShoeBase.lean with faithful countablysupported PMF/discrete-law sourceobjects and strict alternating chronologicalfirst-bipartite-match semantics, then real bashcheck.sh ShoeBase BEFOREAPIrecon/probes. Don't start with an answer-encoding predicate y>=x/256 or an arithmeticlemma-only module. Choose coherent pinned mathlib PMF/Measure representations; all probability spaces/measurability/instances must be genuine, no existence axiom. Later adapt modules based on actual errors and checkpoint frequently. Fullbridge requires arbitrarydiscrete countablesupport (Natcolorcodings plus finiteextension/relabeling invariance as needed), NOTfinite-support-only result. Decide a faithful stochastic model; no libraryAPIguess loop withoutchangedsource.

IMPLEMENTALLordinarypipeline: p_i>=0 sum1, s=sum p_i^2 in(0,1], p_i<=sqrt(s). Conditional independentpair law x_i=p_i^2/s with PMF normalizing/conditional-pair bridge. Infiniteproductiid L_a,R_b lawp, chronological orderL1,R1,L2,R2,...; leastfirstintersectionT, coloruniqueness fromnewshoe, measurablewinningY; a.s.termination via no-match2N subsetallN diagonalpairinequalities with probability(1-s)^N ->0. Null-eventdefinition mustnotchange law. y_i=P(Y=i) genuinePMF/sum1. Pay every infiniteproductfinitecylinder probability, independence/countable sums/continuity/limit rather than assuming a law with desiredproperties.
Largebranchs>=1/64:firstpairequali ->Y=i givesy_i>=p_i^2>=x_i/256 inclpointmasses/boundary. Small0<s<1/64, K=floor1/(4sqrt(s))>=2, K>=1/(8sqrt(s)),K^2s<=1/16. Fixi;zero coordinatebranchseparate. E_ab uniquei atL_a andR_b inK-block, allothercoordinatesnoti; disjoint K^2 events with probabilityp_i^2(1-p_i)^(2K-2). Conditionalproduct-law q_j=p_j/(1-p_i)j!=i, or a fully proved equivalent UNCONDITIONALcylinderestimate (must pay actualprobabilitybridges, not assume it). Finiteunionbound over(K-1)^2non-i crosspairs, conditionalfailure<=s(K-1)^2/(1-p_i)^2<=4/49<1/2. F_ab survives=>ONLYcommonblockcolori, strictchronologicalfirstmatch occurs atmax(2a-1,2b) (bothodd/evenarrivals), nooutsideearlierhistory. Bernoulli gives(1-p_i)^(2K-2)>=1/2, so y_i>=K^2p_i^2/4>=x_i/256. No independence assertion amongdifferentpaircollisionevents needed/allowed. Allfloor/sqrt/division/zero/s1/K2 cases paid.
CountableTVidentity(1/2)sum|x_i-y_i|=1-summin(x_i,y_i) with absolute/nonnegative summability and equivalence to source sup-over-subsets totalvariation. Minorization ->overlap>=1/256 ->D<=255/256 forEVERYp ->strictSUP<=255/256<1, notmerely eachD<1. Prove actual literaluniversal/supremum endpoint; sourcepairsconditionaldrawmodel equivalence, colorrelabelling and masszero extension. Constantoptimality/Conjecture5notclaimed. No conditional y-property endpoint, no unseenlibrarytheorem maskingstochasticbridge. Fullformalobligations remainuntilactuallycompiled/audited. Finishfullpipeline/paper, notjustfoundations.'''
CMDRR='''CONTINUE full MathDB326555NONEXISTENCE, not a newdiscovery or helpercredit. inputs/previous/CHECKPOINT.md and results record exact10greenproductionmodules229declarations, PARTIALreplay only, noendpoint. Working src copies all10 unchanged, immutable referencecopies inputs/baseline-src. NOoldoleanscopied/imported; coldcompile OWN10baselines in listeddependencyorder aftermandatoryinputread/pincheck, using bashcheck.sh. This explicit baselinepreflight is permitted before FIRSTNEWPROOFwrite; don't spend session repeatinggreenbaselines or broadrecon. FIRSTNEWPROOFwrite must be actual remaining cycle/incidence module (e.g.CMDRRCycles.lean) followedbystrictcheck, beforeAPIprobes. Keep same Source/Game/occurrence/Rows/Counts/Repeat/swap/transport definitions; if a fidelitygap requiresa change, editONLYownworkingsrc, documentexactdiff, rebuildallaffectedmodules, neverchange frozenreferencebytes. Roothasnotmathematicallyauditedthesebodies; authorcompiledstateisnotfullfidelityacceptance.

Alreadycompiled: literalunorderedoccurrencemodel/injectivity/count22/11, T/U/Cgenuinepermutations and C(Tx)=Ux, arbitraryrelabelsourcepreservation, synchronizedspouselabelsFin3+Fin2, fullSourcesexswap, row2cyclerepeated-singlerestriction. Mainremainingcontent is centralproof; doNOTreturnmoreboundaryrenaminghelpersinstead.
Finish explicitcanonicalFin5matching and fullSourceequivalence/normalizationassembly; derive uniqueother-singleoppositiontwice ratherthanassumingrecordfield. Structuralorbitpartition on4/5 rowdomains, spousefourcycles:not2+2 sinceeach2cyclerepeatsfemale pairandonlysingles45repeat. Complementaryedgeindicator45=jk on4cycle via degreecounts, no fullschedule enumeration. DefineA/B/zactualoccurrencecounts, payincidencesumover3spousemen:2+A-z=3-B henceA+B=1+z. Any singlerow2cycle must45; remainder3cycleH exhaustsfemale45games throughhim=>A0;other-singlesoppositioncount2 givesB=2-z;2z=1contradiction, thensingle5cycle. ApplyENTIREargument throughpaidSource.swap with explicitcorrespondence to columns, no assumptioncolumnclassification. Signsupportedcycles/disjointsupportrowandcolumnproducts=>signU=signC=-1; Tfixedpointfreeinvolution22cells11two-orbits=>signT=-1; CcomposedT=Uforces+1, contradiction. Assemble universalnoSource/ExistsFiveThree with arbitrary5-elementmale/femaletypes/spousematching3 viaactualtransport. Nocompleteendpointconditionalonunpaidcyclecounting/signfacts, n3roundsassumption, oradditionalLatin/resolvabilityconstraints. Ordinaryfullproofprovided, no newenumeration.

BaselinePINSunchanged; newfullauditmustincludeallbaseline+newprivate/generateddeclarations, exactfinalendpointclosures/bodyoriginDAG, notjustold229transitiveaxioms. Addsubstantivepositive/sourcecontrols andsemanticmutationnegativecontrols. Freshsource-onlyEMPTYbuildreplayALLmodules+checkersupstreamONLY; finishpaperPDFallpagesvisualQA. Retainprevious directcat/sedlogretrievaloutside-runner/permission126/emptywriterrefusal/unboundPACKAGES_ROOTfailures in inheritedprocessrecord, don'teraseorsilentwaive. Newlaneavoidthem. Retainunread2013companion403/prospectivenoveltylimit, no network. Maxonefamily/credit0untilindependentcompleteformalreview/rootacceptance. Fullresolutiontarget, checkpointpaidcontentonrealbuilds.'''

specs=[{'lane':'shoe-pair-discrepancy-formal-sol-r2','id':324571,'source':S,'detail':SHOE},{'lane':'cmdrr-five-three-formal-sol-r3','id':326555,'source':C,'detail':CMDRR}]
ready=[]
for spec in specs:
 L=P/spec['lane'];assert not L.exists();L.mkdir();origins={}
 def cp(src,rel):
  dst=L/rel;dst.parent.mkdir(parents=True,exist_ok=True);shutil.copyfile(src,dst);assert sha(src)==sha(dst);origins[rel]={'path':str(src),'sha256':sha(src)}
 for n in ['bootstrap.py','runner.py','write_lane.py','verify_frozen.py','check.sh','checker.sh']:cp(BASE/n,n)
 for d in ['src','build','audit','receipt','logs','tmp','cache','results','manuscript','output/pdf']:(L/d).mkdir(parents=True,exist_ok=True)
 cp(denpath,'inputs/INHERITED-DENIALS.json')
 cp(C/'PINS.json','PINS.json')
 pins=json.loads((L/'PINS.json').read_text());assert sha(Path(pins['lean_bin']))==pins['lean_sha256'] and sha(Path(pins['leanchecker_bin']))==pins['leanchecker_sha256']
 pack=Path(pins['packages_root']);bins=Path(pins['lean_bin']).parent
 upstream=[str(pack/n/'.lake/build/lib/lean') for n in ['mathlib','batteries','aesop','Qq','proofwidgets','importGraph','LeanSearchClient','plausible']]
 env='#!/bin/bash\nset -eu\nLANE=$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)\nLEAN_BIN='+str(bins)+'\nexport PATH="$LEAN_BIN:$PATH"\nexport LEAN_PATH="$LANE/build:'+':'.join(upstream)+'"\n'
 (L/'env.sh').write_text(env)
 if spec['id']==324571:
  for name in ['REVIEW.md','INDEPENDENT-PROOF.md','DORMANT-OBLIGATIONS.md','keyedreview.json','source-obligation-map.json','SCOPE-COMPARISON.json','access-inventory.json','read-inventory.json','search-inventory.json','registry-comparison.json','failure-inventory.json','resource-inventory.json','SHA256-MANIFEST.json']:
   cp(S/name,'inputs/review/'+name)
  for name in ['literal324571.jsonl','FULLCANDIDATE.md','DORMANT-SOL-FORMAL-PLAN.md','literal-provenance.json','original-fixed20.jsonl','read-inventory.json','access-inventory.json','history-assessment.json','accepted55-routing.json','prior39-routing.json','sources/shoes.pdf','sources/shoes.txt','sources/shoes-final.pdf','sources/shoes-final.txt']:
   cp(S/'inputs'/name,'inputs/author/'+name)
  cp(P/'shoe-pair-discrepancy-source-parent-integration-sol-r1.json','inputs/ROOT-INTEGRATION.json')
 else:
  for q in (C/'inputs').rglob('*'):
   if q.is_file():cp(q,'inputs/original/'+str(q.relative_to(C/'inputs')))
  for name in ['SUMMARY.md','CHECKPOINT.md','PARTIAL-MANUSCRIPT.md','results/326555.json','results/PARTIAL-REPLAY.json','SHA256-MANIFEST.json']:
   cp(C/name,'inputs/previous/'+name)
  state=json.loads((C/'results/326555.json').read_text())
  for mod in state['production_modules']:
   cp(C/'src'/f'{mod}.lean',f'inputs/baseline-src/{mod}.lean');cp(C/'src'/f'{mod}.lean',f'src/{mod}.lean')
  cp(C/'src/CMDRRAudit.lean','inputs/baseline-audit/CMDRRAudit.lean')
  cp(P/'cmdrr-five-three-formal-parent-integration-sol-r2.json','inputs/ROOT-INTEGRATION.json')
 save(L/'INPUT-ORIGINS.json',origins)
 peers=['cover-ratio-primary-comparison-sol-r2']+[s['lane'] for s in specs if s['lane']!=spec['lane']]
 task='FULL literal formalization MathDB'+str(spec['id'])+' in '+str(L)+'. PROTECTED ACTIVE/PLANNED PEERS '+', '.join(peers)+': NOread/hash/glob/list/poll evenmetadata.\n'+COMMON.replace('LANE',str(L))+'\nSPECIFIC SCOPE:\n'+spec['detail']
 (L/'TASK.txt').write_text(task)
 save(L/'ROOT-PREP.json',{'utc':now,'id':spec['id'],'lane':str(L),'provider':'codex','model':'gpt-6.1-sol','reasoning_effort':'high','service_tier':'default','children':False,'network':False,'accepted_new':55,'target_new':60,'credit':0,'no_old_oleans_copied':True,'root_role':'Documentary preparation only','protected_peers':peers})
 # Immutable source archives and own packet; own working sources intentionally editable.
 frozen={str(q):sha(q) for q in spec['source'].rglob('*') if q.is_file()}
 for q in (L/'inputs').rglob('*'):
  if q.is_file():frozen[str(q)]=sha(q)
 for name in ['bootstrap.py','runner.py','write_lane.py','verify_frozen.py','check.sh','checker.sh','PINS.json','env.sh','TASK.txt','INPUT-ORIGINS.json','ROOT-PREP.json']:frozen[str(L/name)]=sha(L/name)
 assert all(sha(Path(s))==v for s,v in frozen.items())
 save(L/'frozen-inputs.json',frozen)
 ready.append({'lane':str(L),'id':spec['id'],'frozen_bindings':len(frozen),'task_sha256':sha(L/'TASK.txt')})
save(ROOT/'shoe-cmdrr-formal-ready.json',{'utc':now,'intakes':intakes,'ready':ready,'other_active_lane':'cover-ratio-primary-comparison-sol-r2','latest_denials':str(denpath),'accepted_new':55,'credit':0})
print(json.dumps({'intakes':intakes,'ready':ready}))
