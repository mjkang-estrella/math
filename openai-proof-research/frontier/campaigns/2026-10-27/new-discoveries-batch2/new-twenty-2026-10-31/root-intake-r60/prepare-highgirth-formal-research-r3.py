"""Prepare an uncounted, offline formal-research packet; root does not run Lean/math."""
import os,resource
os.sched_setaffinity(0,sorted(os.sched_getaffinity(0))[:2])
resource.setrlimit(resource.RLIMIT_CPU,(120,120))
resource.setrlimit(resource.RLIMIT_AS,(6*1024**3,6*1024**3))
from pathlib import Path
import json,hashlib,datetime,shutil,ast
ROOT=Path(__file__).resolve().parent;P=ROOT.parent
H=P/'high-girth-ur-matching-primary-qualification-sol-r2';B=P/'high-girth-ur-matching-source-review-sol-r1';L=P/'high-girth-ur-matching-formal-sol-r3'
def read(p):return json.loads(p.read_text())
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def save(p,v):
 assert not p.exists(),str(p)
 p.write_text(json.dumps(v,indent=2)+'\n')
now=datetime.datetime.now(datetime.timezone.utc).isoformat();assert read(P/'ledger.json')['accepted_new']==57
assert read(ROOT/'highgirth-r2-jaja-r3-r511-intake-report.json')['no_root_mathematics'] and not L.exists()
authorization=dict(utc=now,mathdb_id=338806,status='UNCREDITED_OFFLINE_FORMAL_RESEARCH_AUTHORIZED_SCIENTIFIC_HOLD_PRESERVED',basis='The user explicitly requires literal Lean results and authorizes sustained hypothesis work. Exact original MathDB/v2 scope and the full every-girth ordinary refutation have independent PASS; fresh2019 author thesis restates the broad claim and reviewed primary bodies provide bounded nonmatches. A full certificate is useful feasibility/proof work within that existing authorization.',scientific_qualification='HOLD remains: final2019 body unavailable, current prior/subsumption/significance adjudication unpaid. This authorization is NOT prospective scientific PASS, acceptance, novelty clearance, or a source-access waiver.',substantive_positive='Independent reviewers retain fixedDelta100/everypositiveg robust-ratio refutation of intended broad source conjecture, not finite/domain/degree-growth correction.',substantive_objection='Conventional expander plus classicalUR-obstruction adaptation may still veto credit if a complete actual primary-proof bridge is established. No public/routine exclusion currently authenticated; no worldwide novelty claim.',source_limit='Original1803.11032/finalDOI10.1007/s00373-018-1991-8 ENTIRE work closed to all NEW deliveries after guard-rejected HTTP redirect/logger failure. Explicit copied original/thesis only; no final equivalence asserted.',authorized_next='Fresh GPT-6.1 Sol high/default full literal Lean implementation, all construction/source bridges, audits, controls, empty-build source-only replay and uncredited research manuscript. No network or children.',acceptance='CLOSED: independent full formal/source/audit/paper review and separate final scientific/root adjudication still required. A green Lean theorem alone earns zero.',credit=0,accepted_new=57,target_new=60,previous_accepted=39,root_math_or_Lean_execution=False,review_r1_sha256=sha(B/'REVIEW.md'),proof_r1_sha256=sha(B/'PROOF.md'),review_r2_sha256=sha(H/'REVIEW.md'),review_r2_manifest_sha256=sha(H/'MANIFEST.json'))
save(P/'high-girth-ur-matching-formal-research-authorization-r3.json',authorization)
L.mkdir();origins={}
def copy(src,rel):
 dst=L/rel;dst.parent.mkdir(parents=True,exist_ok=True);shutil.copyfile(src,dst);assert sha(src)==sha(dst);origins[rel]=dict(path=str(src),sha256=sha(src))
for n in ['bootstrap.py','run.py','write_lane.py','verify_frozen.py','model-policy-sol-only.json']:copy(H/n,n)
for n in ['src','build','cache','audit','receipt','logs','results','cleanroom/src','cleanroom/build','manuscript','output/pdf']:(L/n).mkdir(parents=True,exist_ok=True)
for n in ['original338806.raw.jsonl','literal338806.json','provenance338806.json','matching.pdf','matching.txt','matching-metadata.html','accepted57-scopes.json','prior39-scopes.json']:copy(H/'inputs'/n,'inputs/'+n)
for n in ['FULLCANDIDATE.md','DORMANT-SOL-FORMAL-PLAN.md']:copy(B/'inputs'/n,'inputs/author/'+n)
for n in ['REVIEW.md','PROOF.md','review.json','source-map.json','scope-comparisons.json']:copy(B/n,'inputs/review-r1/'+n)
for n in ['REVIEW.md','PROOF.md','GAP.md','review.json','source-map.json','NETWORK-STOP.json']:copy(H/n,'inputs/review-r2/'+n)
for n in ['restricted-matchings.pdf','restricted-matchings.txt','goddard2005.pdf','goddard2005.txt']:copy(H/'sources'/n,'inputs/sources/'+n)
copy(P/'high-girth-ur-matching-formal-research-authorization-r3.json','inputs/ROOT-AUTHORIZATION.json');copy(ROOT/'inherited-denials-r524.json','inputs/INHERITED-DENIALS.json')
binpath=Path('/home/mj-kang/Documents/Dev/math/dlp-research/.tools/lean-4.34.1-linux/bin');pack=Path('/home/mj-kang/Documents/Dev/math/openai-proof-research/frontier/campaigns/2026-10-14/formal/.lake/packages')
assert sha(binpath/'lean')=='e8baaa71855a616dc351028f3ad2200051b0671f423a1696a100e809302d5550'
assert sha(binpath/'leanchecker')=='ccef1bfe9bfeecea65137d94a69033c1a89f360711f50fa3178e7ba3e696fcbe'
packages=['mathlib','batteries','aesop','Qq','proofwidgets','importGraph','LeanSearchClient','plausible']
upstream=[str(pack/n/'.lake/build/lib/lean') for n in packages]
assert all(Path(x).is_dir() for x in upstream)
pins=dict(lean_version='4.34.1',mathlib_revision='d13f23b723b8a846827a245b89c10fc7d3f11612',lean_bin=str(binpath/'lean'),lean_sha256=sha(binpath/'lean'),leanchecker_bin=str(binpath/'leanchecker'),leanchecker_sha256=sha(binpath/'leanchecker'),packages_root=str(pack),upstream_lean_paths=upstream,mathlib_source=str(pack/'mathlib'),mathlib_metadata_sha256={str(q.relative_to(pack/'mathlib')):sha(q) for q in [pack/'mathlib/Mathlib.lean',pack/'mathlib/lake-manifest.json'] if q.is_file()},pin_limits='Root hashed binaries and available upstream source metadata, did NOT execute Lean/git or attest all upstream olean origins. Worker verifies runtime version/pin metadata before compilation; accepted pinned upstream oleans trusted. Never overwrite PINS.json; record discovered verification limits separately.')
save(L/'PINS.json',pins)
command='''import os,re,json,hashlib,subprocess,sys,shutil
from pathlib import Path
p=Path(__file__).resolve().parent
pins=json.loads((p/'PINS.json').read_text())
mode=os.environ['FORMAL_OPERATION'];module=os.environ['FORMAL_MODULE']
assert mode in ['compile','check'] and re.fullmatch(r'[A-Za-z][A-Za-z0-9_]*',module)
def sha(q):return hashlib.sha256(q.read_bytes()).hexdigest()
assert sha(Path(pins['lean_bin']))==pins['lean_sha256'] and sha(Path(pins['leanchecker_bin']))==pins['leanchecker_sha256']
source=p/'src'/(module+'.lean');olean=p/'build'/(module+'.olean')
assert source.is_file();before=sha(source)
env=dict(os.environ);env['PATH']=str(Path(pins['lean_bin']).parent)+os.pathsep+env.get('PATH','');env['LEAN_PATH']=os.pathsep.join([str(p/'build')]+pins['upstream_lean_paths']);env['LEAN_NUM_THREADS']='1'
prior=sha(olean) if olean.exists() else None
if mode=='compile':
 if olean.exists():
  archive=p/'cache'/(module+'.'+prior+'.olean')
  if not archive.exists():shutil.copyfile(olean,archive)
  olean.unlink()
 args=[pins['lean_bin'],'-j1','-M3500','-DwarningAsError=true','-o',str(olean),str(source)]
else:
 assert olean.is_file(),'Kernel checker requires actual production olean'
 args=[pins['leanchecker_bin'],module]
r=subprocess.run(args,cwd=p,env=env,text=True,capture_output=True)
sys.stdout.write(r.stdout);sys.stderr.write(r.stderr)
after=sha(source);out=sha(olean) if olean.exists() else None
print(json.dumps(dict(stage=mode,module=module,argv=args,exit=r.returncode,source_sha256_before=before,source_sha256_after=after,olean_sha256_before=prior,olean_sha256_after=out,LEAN_PATH=env['LEAN_PATH'],LEAN_NUM_THREADS=1)))
assert before==after,'Source changed during compile/check'
if r.returncode==0:
 assert out is not None,'No fresh olean produced'
 if mode=='check':assert prior==out,'Checker changed olean'
raise SystemExit(r.returncode)
'''
ast.parse(command);(L/'formal_command.py').write_text(command)
for filename,operation in [('check.sh','compile'),('checker.sh','check')]:
 shell='#!/bin/bash\nset -eu\nexport FORMAL_OPERATION='+operation+'\nexport FORMAL_MODULE="${1:?module name required}"\nexport FORMAL_ROOT="$(cd "$(dirname "$0")" && pwd)"\nexec timeout 140 python3 -I -B "$FORMAL_ROOT/run.py" "${2:?unique receipt label required}" <<\'PY\'\nimport os,runpy\nrunpy.run_path(os.path.join(os.environ["FORMAL_ROOT"],"formal_command.py"),run_name="__main__")\nPY\n'
 (L/filename).write_text(shell);(L/filename).chmod(0o755)
task=f'''You are the sole worker, ONLY GPT-6.1 Sol HIGH reasoning DEFAULT speed. No children/provider/model fallback. ROOT explicitly authorizes UNCREDITED full Lean research for338806 while SCIENTIFIC HOLD REMAINS. Read inputs/ROOT-AUTHORIZATION.json: this is NOT scientificPASS/acceptance/novelty/source-access waiver. Independent ordinary/literal PASS already paid. Do the FULL literal proof, audits, replay and paper, not a model-only milestone. Keep progressing dependency-ordered and persist actual strict-green checkpoints if interrupted. Never selfcredit;57/60 beyond39,96total unchanged.

FIRST shell command EXACTLY:
timeout 20 python3 -I -B {L}/bootstrap.py
Read complete printedAGENTS/TASK; preservefirstreceipt. SECOND shell command EXACTLY:
timeout 140 python3 -I -B {L}/verify_frozen.py before
No extra punctuation/chaining. All other substantive source/API/math/doc/compile/audit/render subprocess work UNDER immutable ABSOLUTE {L}/run.py UNIQUE_LABEL Python stdin, outertimeout140, or supplied strict check/checker wrappers. Authored sources/products via ABSOLUTE write_lane.py; compiler-generated build/cache/audit/replay outputs and runner-owned receipts/logs are explicit derived-artifact exceptions. Frozen helpers/PINS/inputs/TASK immutable. Actual frozen/protected/cap breach STOP/disclose,no reset; ordinary diagnostic/source/schema/dependency failure may be repaired from persisted evidence. No /tmp/shared/parent writes, git/install/account/browser/network/search/HTTP/externalmessage/background jobs. Offline ONLY, even if source gaps tempt retrieval. ALL other campaign/formal/code-loop/Polynexus/crown/bunkbed/tournament/Hat bodies and integrations protected. Active peers product-measure-dimension-source-review-sol-r1 andexpanded-corpus-r512 ENTIRELY protected incl stat/read/hash/list/glob/poll/reservations/flat integration. No legacy source/olean/import/build paths. Only own copies/products/helpers and PINNED upstream mathlib/core API/source/metadata may be accessed. Embedded provenance paths are NOT permission to follow.

Afterfirsttwocommands read PINS, ROOTauthorization, exactraw/literal/provenance, authorproof/plan and BOTH independent reviews/PROOF/GAP/source maps in full manageable segments. Read actual copied original p1/p3 and thesis Chapter6 Conj6.4 scope; own relevant PDFs may be rendered/viewed offline, not retrieved again. Source's actual finalDOI10.1007/s00373-018-1991-8/original1803.11032 ENTIREworkclosed afterguardrejectHTTP/loggerfailure; copiedpredeliveryoriginal/thesis notfinalequivalence. Thesis2019 independentlyretains broadallDelta claim; this supports literal fidelity, notworldwidepriority. Scientific/source/prior/significance HOLD MUST remaininresults/manuscript,mayveto acceptance. No claim of final-body/current-registry clearance. Independent formal/source/body-audit/paper review and root scientific/credit adjudication remain separate/unpaid.

Pinned Lean4.34.1 andmathlibd13f23b723b8a846827a245b89c10fc7d3f11612; verify actual binaryhash/runtimeversion and availableupstream pinmetadata UNDER runner before compilation, no gitbinary/networkfetch. Preserve limits if metadata cannot attest revision; do not call unverifiedpinsPASS. PINS expectedsha paths immutable; do NOT overwrite it with generatedstate. Upstreamprebuiltoleans trusted, notrootrebuilt/attested. READ only upstream pinned APIs, no othermathprojects.

FIRST NEW-PROOF operation aftermandatoryinput/pinreading: WRITE faithful source model src/URMatchingBase.lean, then run {L}/check.sh URMatchingBase UNIQUE_LABEL immediately before broad API/probe tours. Real compile failures retained. Then diagnostic-driven pinnedAPIlookup/probes permitted UNDERrunner. Use targetedimports; no baseline/old formalreplay. Wrapper signature check.sh MODULE UNIQUE_LABEL, checker.sh MODULE UNIQUE_LABEL. Both run actualpinnedbinaries, ownbuild+upstreamonlyLEAN_PATH, -j1 -M3500 -DwarningAsError=true forcompile, LEAN_NUM_THREADS1. Old own olean archived beforefreshcompile; trueexit andbefore/after source/oleanhashes printedinown log. Checker by MODULENAME, notfile. Freeze wrappers; ifCLI surface issue is discovered, recordit and use exactpinned invocationunder runner with samecaps, no helpermutation/stalepass. Everyproductionmodule needsstrictcompileANDkernelchecker.

LITERAL MODEL: finite simpleundirectedgraphs, actualfinite neighborcardinality maximumdegree, matching as actual disjointgraph edges, nu as maximumcardinalityofALLmatchings, nu_ur as maximumcardinalityofmatchingsunique amongALLmatchingscoveringexactlysamevertices. UR is NOT inducedmatching/acyclicinducedforest or DAG bydefinition. Prove all representation/quotient/bipartite-edge/standard-matching-number bridges; do not sneak neededacyclicity/noholes/expansion/cyclecounts/ratio into fields or hypotheses. Girth>=g must genuinely mean no simplecycle oflength<g, with forestinfinitegirth handled andstandardgirth/cyclepredicate/sourceconvention bridge paid. Maximumdegree boundmustapplyallvertices, source'ssubcubic/connected/regularsubtheoremsnotadded. Universal sourceclaim: forall epsilon:Real>0,forallpositiveDelta,existspositiveg,forallfinitegraphs(maxdegree<=Delta,girth>=g), cast nu_ur>=(1-epsilon)*cast nu. Exactnegation delivered via epsilon1/4,Delta100,forallpositiveg finitebipartitewitness,notjustoneN/g/helper. Ifown faithful matching/girth definitions used because pinnedAPI incomplete, prove generic source/standardcorrespondences, not proxy/circular definitions. ModelmaywitnessFin-labelsubfamilybutfinalnegationmustquantifythe full actualsourceclass. Universe/relabeling/canonicalcoding bridge paid, no weakened conclusion.

IMPLEMENT FULL ORDINARY PROOF (existingindependentPROOF is authoritative ordinary evidence, not a Lean premise):
1 URmatching matchededge-indexdigraph i->j iff crossedgeexists,i!=j. Directedcycle producesdistinctmatchingonsamecoveredvertices; finiteDAGtopologicalorder => lastfloor(m/2) matchedX versusfirstfloor(m/2)matchedY emptyrectangle. Pay disjointindices,orientation,partialmatchings,bipartite labeling/transport,oddm.
2 Finite uniform space of100INDEPENDENTbijections X->Y, |X|=|Y|=N,4dividesN. Coloredmultigraph genuinepermutationgraphs; firstcolorperfectmatching; maxmultidegree100. ForfixedA,B sizeN/4 exactavoidancefalling-factorialratio <=exp(-N/16), or a FULLYPROVED equivalentrational/geometricbound sufficientforalllargeN. CountallA/Bchoices<=4^N,independencecolors =>bad-holeprob<=4^N exp(-100N/16)<1/4 eventually. No importedunprovedexpander, computationalenumeration orprobabilisticconditioning.
3 Coloredclosedcyclewitnesslength2l,l1..h=max(1,ceil(g/2)); l1twoDISTINCTcolorssamepairparallelwitness; longerlistsdistinctX/Y andcolorededges. Number<=N^(2l)100^(2l); inconsistentonecolorprescriptionsprob0, consistentrpairprob1/(N)_r. N>=4h =>E W_l<=(200)^(2l). WeightedS=sum2lW_l boundsunionofdeletedvertices; finiteB_h=sum2l200^(2l),choose4|N,N>400B_h andholebounds. Markov+unionbound probabilitygood>0 =>actualtuple. Payfiniteprobabilitycounting/cardinals/expectation/strictbounds/allg,not axiomaticexistence oranswerencoding.
4 DeleteALLverticesonANYcountedshortcycle/parallelwitness, INDUCEDsurvivor. AtmostS<N/100 deleted; simple,bipartite,maxdegree<=100,girth>2h>=g. No newemptyrectangleamongSURVIVORS. Firstcolorlosesatmostoneedgeperdeletedvertex =>nu>99N/100 despiteunequalsides. UR>=N/2 =>floor(m/2)>=N/4 by4|N,rectanglecontradiction =>nu_ur<N/2<(3/4)nu. Allstrict/nonvacuous/forest/smallg andsourceinequalitycasts paid. DoNOT useedgedeletionfornoholes orclaimsurvivingperfectmatching. DoNOT replaceallg byfiniteenumeration/computationalcertificate.
5 Assemble actualall-sourcequantifiernegation withall source/representation/girth/maximummatching/probability bridges. Allowedconstants100/1/4, stronger50/99ratio notextra credit. Standardtactics omega/norm_num/ring/finiteBoolean kerneldecide mayproducekernelproofs; no native_decide/nativecompute axiom/external solver/CAS/Python mathenumeration/numericalevidence/sorry/admit/addedaxiom/unsafe/partial/extern/implementedBy. Onlypropext/Classical.choice/Quot.sound axioms.

Resourcecaps affinity<=2,childCPU115/supervisor120,AS6GiB,sampledgroupRSS6GiB,deadline130/outer140,arena2. StandalonefrozenverifierCPU120exceptionnotnested. No uncappedLean/API/read/render subprocess. PreserveEVERYfailedattempt/diagnostic/nonzeroactualexit,sourceSHA/oleanSHA/logreceipt; no overwritefailedpasshistory. Alljobsreaped; no universalcgroup/native/transient/writer/supervisorpeakclaims. No repeatedunchangedfailedcompile; repairfromactualdiagnostics. Persist CHECKPOINT andresultunpaidledger atEVERY strictgreenmodule. Ifinterrupted/incomplete, handbackexactpaid/unpaidtheorems+lastrealexits/paths; no futuretense"writingnow"handoff/nohelpercredit.

AUDIT/REPLAY/CONTROLS: scoped#printaxioms ALLnewproductiondecls; fulltransitivebody-origin/implementationmetadata/DAGaudit inclprivate/generateddecls andallendpointclosures. Partition/shardauditsunderresourcecaps ratherthanrepeatingmemoryblowups. Printdefinitionsneededfidelityandactualcounts,notextrapolation. Onlypermittedaxiomtrio; distinguishtrustedupstreamtacticimplementationfromproductionproofdependencies. Meaningfulnonvacuity/semanticpositivecontrols andisolatednegativecontrols thatMUSTfailunderintentionalmodels/statementmutations,alltrueexitsretained. Fresh owncleanroomsource-onlycopies hash-identical,EMPTYbuild,pinnedupstreamONLYLEAN_PATH,no production/legacy/authoroleanimports; everymodulerebuiltstrictANDkernelchecked,hashesrecheckedAFTERchecker. FullDAGsource-to-theoremfidelitynotjusttopaxioms.

PAPER: readablecompleteUNCREDITEDresearchmanuscript exactsourceclaim/model,ordinaryallgproof,fullformalendpoint,allbridges,audit/replay/controlactualevidence andLIMITS. ExplicitscientificHOLD/finalaccess/prior/significanceroutineobjection,noveltyboundednotworldwidepriority; sourcecurrentfailureisnotpublicresolution. PDFskill /home/mj-kang/.codex/plugins/cache/openai-primary-runtime/pdf/26.1103.10131/skills/pdf/SKILL.md permitted,announce/read/followbeforeauthoring. No installsneeded; useavailabletools. RenderEVERYfinalPDFpageandpersonallyviewownimages; read-onlynativepresentationofownpermittedrendersauthorized,nottelemetryproof. Outputunderownoutput/pdf,sourceunderownmanuscript. No publication.

Closeout: results/338806.json credit0/57of60, SUMMARY.md/CHECKPOINT.md, source-to-literalmap/exactunpaidlist, allreceipts/logs/source/olean/paper/renders/audits/replay/controlhashes. Standaloneverify_frozen.py afterTHENexhaustiveOWNbyteSHAmanifest inclALLcompletedreceiptJSONs/helper/PINS/inputs/products/plans/evidence. Preciselyname terminalnoncircularself-exclusionsonly, no externalfrozenpeerpaths/no laterfrozenwrites. PINS/bootstrap/inputimmutabilitycritical. RootandindependentreviewacceptanceremainUNPAID; neverclaimearnedcredit/scientificPASSbecauseLeangreen.
'''
(L/'TASK.txt').write_text(task);save(L/'INPUT-ORIGINS.json',origins)
save(L/'ROOT-PREP.json',dict(utc=now,lane=str(L),mathdb_id=338806,model='gpt-6.1-sol',reasoning='high',service='default',network=False,children=False,credit=0,accepted_new=57,scientific_hold=True,root_execution='Documentary helpers and packet preparation only; no Lean/math execution',protected_active_peers=['product-measure-dimension-source-review-sol-r1','expanded-corpus-r512']))
ff=[q for q in L.rglob('*') if q.is_file()];save(L/'frozen-inputs.json',{str(q):sha(q) for q in ff})
ready=dict(utc=now,lane=str(L),mathdb_id=338806,task_sha256=sha(L/'TASK.txt'),frozen_bindings=len(ff),model='gpt-6.1-sol',reasoning='high',service='default',credit=0,accepted_new=57,scientific_hold=True,authorization=str(P/'high-girth-ur-matching-formal-research-authorization-r3.json'),protected_peers=['product-measure-dimension-source-review-sol-r1','expanded-corpus-r512'])
save(ROOT/'high-girth-ur-matching-formal-r3-ready.json',ready);save(ROOT/'selection-routing-high-girth-ur-matching-formal-r3.json',dict(ids=[338806],sources=['https://arxiv.org/abs/1803.11032'],lane=str(L),task_sha256=ready['task_sha256'],metadata_only=True))
print(json.dumps(dict(ready=ready,credit=0,accepted_new=57,root_no_Lean_execution=True)))
