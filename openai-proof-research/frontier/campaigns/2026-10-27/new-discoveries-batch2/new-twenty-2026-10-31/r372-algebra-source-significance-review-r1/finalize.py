import os,resource
os.sched_setaffinity(0,sorted(os.sched_getaffinity(0))[:2]);resource.setrlimit(resource.RLIMIT_CPU,(120,120));resource.setrlimit(resource.RLIMIT_AS,(6*1024**3,6*1024**3))
import sys,pathlib,json,time,hashlib,re
sys.path.insert(0,str(pathlib.Path(__file__).resolve().parent));import review_ops as r
report=r.read(r.LANE/'REVIEW.md').decode(); assert 'a=X^2' in report and '√I' in report
records={}
for id in ('381265','331096'):
 raw=r.read(r.BASE/'raw'/f'{id}.jsonl'); j=json.loads(raw)
 records[id]=dict(mathdb_id=int(id),credit=0,campaign_count='52/60 unchanged',raw_sha256=hashlib.sha256(raw).hexdigest(),literal_statement=j['statement'],source=j['source_url'],decision='INDEPENDENT_ROUTINE_ADAPTATION_EXCLUSION_RECOMMENDED_TO_ROOT',root_adopted=False,proof_evidence='REVIEW.md',gates=dict(fidelity='PASS_WITH_EXPLICIT_SOURCE_SCOPE',ordinary_correctness='PASS',final_version='WU_JOURNAL_RELEVANT_BODY_READ_CORRECTION_COVERAGE_BOUNDED' if id=='381265' else 'HOLD_FINAL_PUBLICATION_CORRECTIONS',exact_prior_resolution='HOLD',novelty='NO_WORLDWIDE_CLAIM',significance='RECOMMEND_ROUTINE_EXCLUSION_AFTER_FULL_BRIDGE',formal='NOT_RUN',Pi='DORMANT_DO_NOT_DISPATCH',independent_ordinary_review='COMPLETED',operational='LIMITED_HOLD_DISCLOSED_TELEMETRY_GAPS',acceptance='NOT_ACCEPTED'),residuals=['Exact prior endpoint and individual registry commit chronology not authenticated','Subsequent correction/citing coverage not exhaustive','No formal endpoint or replay','Root adjudication remains outstanding','Operational telemetry gaps remain disclosed'])
records['381265'].update(bridge_steps=['source finite directed multigraph with loops','H0=B/I and actual S-module annihilator I∩S','padded monic list matching in every prime quotient, all characteristics','coordinate-equality quotient polynomial over Z','integral radical finite intersection','exact contraction to all selected edge subrings','same retained class counts over Z/Q','bottom-prime finite-intersection chain argument','actual localization membership proof','empty E, edgeless, loops and isolated vertices'],strongest_objection='Complex geometry does not control vertical components or contraction; source explicitly conjectures equality.',rebuttal='Every-prime matching excludes unlisted vertical components; restricted coordinate map has exact polynomial image. Full bridge in REVIEW.md.',added_vs_printed='Integral domain matching/radical and contraction-component calculation added; printed family, equations, annihilator and polynomial dimensions retained.')
records['331096'].update(bridge_steps=['2011 journal ring Z[X,Y]/(X^3,XY)','finite-divisor descent gives union by maximal principal ideals in I','irredundancy and compulsory minimal members','X^3 and XY force simultaneous infinite gcd X','a=X^2 gives gcd X','x and x² both nonzero zero-divisors','x annihilates x² but not x'],interior_witness=dict(D='Z[X,Y]',I='(X^3,XY)',a='X^2',simultaneous_gcd='X',annihilator_separator='x',both_sides_vertices=True),strongest_objection='Old example does not print a minimal union or refutation; author Y witness reaches undefined unit bracket.',rebuttal='Full minimal-union proof and two-interior-vertex X²/X witness supplied independently.',added_vs_printed='Ring and class definitions printed in earlier journal; minimal union, gcd calculation and interior witness added.')
jobs=[];jobs.append(r.write('review.json',json.dumps(records,indent=2,ensure_ascii=False)))
# Aggregate only this lane's receipts and the supplied frozen map; no author directory scan.
receipts=[]
for p in sorted(r.LANE.iterdir()):
 if p.name.startswith(('receipt-','http-')) and p.suffix=='.json':
  receipts.append(dict(file=p.name,data=json.loads(r.read(p))))
http=[q for x in receipts for q in x['data'].get('HTTP',[])];assert len(http)==7
jobs.append(r.write('inventories-accounting.json',json.dumps(dict(receipts=receipts,direct_GET_explicit_calls=len(http),search_batches=3,queries=10,redirect_hops='not instrumented',search_transport='no resource/HTTP telemetry exposed',semantic_depth='See REVIEW.md exact sections; full bytes do not mean whole-source semantic reading',operational_gaps=['initial capped inventory read not individually logged','direct script writer invocations lack standalone telemetry','stdin transfer may precede child RSS samples','receipt exit_intent is not actual measured exit','tool search internal telemetry unavailable'],observed_tool_exits=dict(bootstrap=0,frozen_before=0,processing='all observed completed0 except two inspect import failures1 before source reads',writer='all observed completed0',finalizer='not yet observed; do not fabricate current exit'),jobs=jobs),indent=2)))
jobs.append(r.write('finalize-resource.json',json.dumps(dict(reads=r.reads,jobs=jobs,usage=list(resource.getrusage(resource.RUSAGE_SELF)),affinity=sorted(os.sched_getaffinity(0)),exit_note='current exit not yet observed'),indent=2)))
# Verify actual bytes, excluding circular/future outputs.
excluded={'actual-hashes.json','actual-hashes-verification.json','final-audit-receipt.json','frozen-after.json'}
files={}
for p in sorted(r.LANE.rglob('*')):
 if p.is_file() and p.name not in excluded:
  assert not p.is_symlink(); b=r.read(p); files[str(p.relative_to(r.LANE))]=hashlib.sha256(b).hexdigest()
manifest=dict(algorithm='sha256',files=files,excluded=sorted(excluded),scope='own resolved lane only; frozen80 independently verified by supplied verifier')
print(json.dumps(r.write('actual-hashes.json',json.dumps(manifest,indent=2))))
bad=[]
for n,h in files.items():
 if hashlib.sha256(r.read(r.LANE/n)).hexdigest()!=h:bad.append(n)
print(json.dumps(r.write('actual-hashes-verification.json',json.dumps(dict(count=len(files),mismatches=bad,recomputed_from_actual_bytes=True,utc_epoch=time.time()),indent=2))));assert not bad
print(json.dumps(r.write('final-audit-receipt.json',json.dumps(dict(reads=r.reads,jobs=jobs,usage=list(resource.getrusage(resource.RUSAGE_SELF)),manifest_count=len(files),exit_note='actual tool return code controls; not predicted'),indent=2))))
print('VERIFIED',len(files),'hashes; final frozen-after check remains required')
