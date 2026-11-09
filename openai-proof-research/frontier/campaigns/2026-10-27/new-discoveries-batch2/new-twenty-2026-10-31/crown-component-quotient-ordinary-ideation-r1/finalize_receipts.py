import os, resource
os.sched_setaffinity(0, sorted(os.sched_getaffinity(0))[:2])
resource.setrlimit(resource.RLIMIT_CPU, (10,10))
resource.setrlimit(resource.RLIMIT_AS, (512*1024**2,512*1024**2))
from pathlib import Path
import hashlib, json, subprocess, sys, time, datetime
lane=Path(__file__).resolve().parent
start=time.monotonic()
def utc(): return datetime.datetime.now(datetime.timezone.utc).isoformat()
started=utc(); jobs=[]
def sha(data): return hashlib.sha256(data).hexdigest()
def write(name,obj):
    text=json.dumps(obj,indent=2,ensure_ascii=False)+'\n'
    p=subprocess.run([sys.executable,'-I','-B',str(lane/'write_lane.py'),name],input=text,text=True,capture_output=True,timeout=15)
    jobs.append({'operation':'write_lane '+name,'exit':p.returncode,'joined':True})
    if p.returncode: raise RuntimeError(p.stderr)
base=lane.parent
specs=[
('crown-vnumber-root-proof-r1/ORDINARY-PROOF.md','Full ordinary mathematical proof read.'),
('crown-vnumber-manuscript-parent-review-r2/paper.txt','Whole text processed once; initial combined output truncated. Pages 1-3 reread separately for exact definitions and classification; later displayed pages supplied main proof and scope. No manuscript edit.'),
('crown-vnumber-manuscript-math-review-r1/REVIEW.md','Full completed ordinary review read.'),
('crown-fullside-primality-formal-pi-r18/src/CrownVAlg.lean','Mathematical definitions: coordinate ring, minor, coordGens, compMinors, Pc. No implementation/API investigation.'),
('crown-fullside-primality-formal-pi-r18/src/CrownVCut.lean','File processed once, combined output partly truncated; family, cut and FamPrime specifications separately reread. Read only as mathematical specification.'),
('crown-fullside-primality-formal-pi-r18/src/CrownVFullSide.lean','Full completed file separately displayed; mathematical full-side coordinate-ideal specification only.')]
reads=[]
for rel,depth in specs:
    p=base/rel; data=p.read_bytes(); reads.append({'path':str(p),'bytes':len(data),'sha256':sha(data),'read_depth':depth,'network':False})
boot=json.loads((lane/'bootstrap-receipt.json').read_text())
for entry in boot['reads']:
    p=Path(entry['path']); data=p.read_bytes(); reads.append({'path':str(p),'bytes':len(data),'sha256':sha(data),'read_depth':'Full applicable instructions read by bootstrap.'})
write('read-inventory.json',{'MathDB':369163,'reads':reads,'other_reads':'Lane bootstrap.py, verify_frozen.py, write_lane.py and bootstrap receipt; supplied frozen verifier integrity-read its exact 975-entry manifest. No external source requests.','protected_active_lanes':'Not read, globbed, custom-hashed or polled.','authorization':'Exact TASK-authorized completed mathematical inputs only; no recursive lane search.'})
write('findings369163.json',{'369163':{'status':'ORDINARY_PROOF','credit':0,'supplied_campaign_count':'52/60 unchanged','auxiliary':True,'single_block':'Complete finite swap certificate, decreasing weight, explicit greedy normal form, unique terminal monomial and arbitrary coefficient extraction over every commutative coefficient ring.','partition_extension':'Complete original-ideal kernel equality for independent block parameters and killed coordinates, including singleton and empty cases.','actual_Pc':'SameC classes give exactly the original completed-component generators; proper/prime over fields.','families':'Empty cut; one-deleted-side star including its central vertex plus isolate; mixed distinct-index two-edge blocks.','review':{'kind':'Adversarial self-review only','mathematics':'PASS within stated ordinary scope','formal_endpoint':'UNPAID','independent_review':'Not performed'},'residuals':['Formal implementation of the constructive bridge','Separate radical decomposition/classification/minimality formal bridges','Separate local-v lower bounds, witnesses and final formal endpoint'],'process_findings':['Two early cat read commands lacked pre-read caps; documented deviation.','No retrospective sampled RSS telemetry claimed.'],'novelty':'Standard algebra support; no novelty or acceptance claim.'}})
u=resource.getrusage(resource.RUSAGE_SELF); c=resource.getrusage(resource.RUSAGE_CHILDREN)
write('process-receipts.json',{'MathDB':369163,'final_source_processing_start_UTC':started,'snapshot_UTC':utc(),'affinity':sorted(os.sched_getaffinity(0)),'CPU_limit_seconds':10,'AS_limit_bytes':512*1024**2,'external_timeout_seconds':20,'self_CPU_seconds':u.ru_utime+u.ru_stime,'self_high_water_RSS_KiB':u.ru_maxrss,'joined_child_CPU_seconds_at_snapshot':c.ru_utime+c.ru_stime,'joined_child_high_water_RSS_KiB_at_snapshot':c.ru_maxrss,'wall_seconds_at_snapshot':time.monotonic()-start,'metrics_scope':'This final source-processing process, not historical commands, process group or cgroup. RSS is high-water rusage, not sampled RSS. Child metrics cover writer children completed before snapshot.','completed_writer_jobs_at_snapshot':jobs.copy(),'first_command':'Required timeout20 bootstrap.py .; exit0; first immutable bootstrap-receipt preserved.','second_command':'Required timeout140 verify_frozen.py before; exit0; count975, no mismatches.','other_calls':'All synchronous exec commands returned exit0. No asynchronous sessions, children for mathematics, background jobs, network requests or browser actions. Writer subprocesses here are synchronous source/receipt processing only.','deviation':'The two early cat source-read commands had no explicit CPU/AS/affinity caps. Their resource usage was not sampled; no retroactive compliance claimed. All later custom Python reads set caps before reads. Shell/timeout wrappers not attested capped.','network_receipts':[]})
files=['TASK.txt','bootstrap.py','verify_frozen.py','write_lane.py','frozen-inputs.json','bootstrap-receipt.json','frozen-before.json','frozen-after.json','SINGLE-BLOCK-MILESTONE.md','PROOF.md','REVIEW.md','NEXT-PI-BRIEF.md','finalize_receipts.py','read-inventory.json','findings369163.json','process-receipts.json']
entries={name:{'bytes':len((lane/name).read_bytes()),'sha256':sha((lane/name).read_bytes())} for name in files}
write('output-manifest.json',{'algorithm':'SHA-256','entries':entries,'self_exclusions':['output-manifest.json','manifest-verification.json'],'reason':'Manifest and its verification receipt are outside the hashed set to avoid a circular self-hash; all other named lane inputs, controls and deliverables included.'})
m=json.loads((lane/'output-manifest.json').read_text()); bad=[]
for name,entry in m['entries'].items():
    data=(lane/name).read_bytes()
    if sha(data)!=entry['sha256'] or len(data)!=entry['bytes']: bad.append(name)
write('manifest-verification.json',{'UTC':utc(),'checked_entries':len(entries),'mismatches':bad,'status':'PASS' if not bad else 'FAIL','output_manifest_sha256':sha((lane/'output-manifest.json').read_bytes()),'jobs':'All writer subprocesses synchronously joined; no background tasks.'})
print(json.dumps({'manifest_entries':len(entries),'mismatches':bad,'completed_writes':jobs,'finished_UTC':utc()}))
if bad: raise SystemExit(1)
