import os,resource
os.sched_setaffinity(0,sorted(os.sched_getaffinity(0))[:2])
resource.setrlimit(resource.RLIMIT_CPU,(120,120))
resource.setrlimit(resource.RLIMIT_AS,(6*1024**3,6*1024**3))
from pathlib import Path
import json,hashlib,datetime,collections,shutil
P=Path(__file__).resolve().parent.parent;ROOT=P/'root-intake-r60'
R=P/'shoe-pair-discrepancy-formal-independent-review-sol-r5'
L=P/'shoe-pair-discrepancy-formal-independent-review-sol-r6'
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def save(p,d):
 assert not p.exists(),str(p)
 p.parent.mkdir(parents=True,exist_ok=True);p.write_text(json.dumps(d,indent=2)+'\n')
assert not L.exists()
assert json.loads((P/'ledger.json').read_text())['accepted_new']==55
now=datetime.datetime.now(datetime.timezone.utc).isoformat()
m=json.loads((R/'SHA256-MANIFEST.json').read_text());files=m['files']
assert len(files)==494 and all(sha(R/n)==v['sha256'] for n,v in files.items())
frozen=json.loads((R/'frozen-inputs.json').read_text());assert len(frozen)==1596
for n,v in frozen.items():
 assert 'cmdrr-five-three-formal-independent-review-sol-r5' not in n and 'binary-projection-ratio-source-review-sol-r1' not in n
 assert sha(Path(n))==v
after=json.loads((R/'frozen-after.json').read_text());assert after['count']==1596 and after['mismatches']==[]
recs=[]
for n in [n for n in files if n.startswith('receipt/') and n.endswith('.json')]+[n for n in m['exact_terminal_self_exclusions'] if n.startswith('receipt/')]:
 j=json.loads((R/n).read_text());assert j['group_members_left']==[] and sha(Path(j['log']))==j['log_sha256']
 recs.append(dict(path=n,sha256=sha(R/n),label=j['label'],exit=j['exit'],group_members_left=j['group_members_left']))
assert len(recs)==10 and all(x['exit']==0 for x in recs)
assert not list((R/'build').iterdir())
parent=P/'shoe-pair-discrepancy-formal-independent-review-parent-integration-sol-r5.json'
adjudication=dict(utc=now,mathdb_id=324571,review_lane=str(R),manifest_files_verified=len(files),manifest_sha256=sha(R/'SHA256-MANIFEST.json'),manifest_mismatches=[],frozen_verified=len(frozen),frozen_mismatches=[],frozen_after=after,completed_receipts=recs,
 status='INCOMPLETE_INDEPENDENT_REVIEW__NO_COMPILATION_OR_TECHNICAL_CERTIFICATION',
 actual_unpaid='All substantive proof bodies, strict/checker/replay, origin DAG/closure audit, controls, full source comparison, prior/family and all five paper pages remain unpaid.',
 process_observation='Two guessed own-lane log paths: singular log/ path rejected by containment assertion, own logs/setup_read.log absent so FileNotFoundError. Both failed before displaying file content. Exact tool events retained in root-intake-r60/shoe-review-r5-activity-evidence.json. Later own setup/source reads do not retroactively satisfy the known-log restriction.',
 root_process_adjudication='Retain as a known-log-only procedural deviation, not universal compliance PASS. Observed failed attempts do not establish protected-data access, frozen modification, compiler execution or mathematical contamination. They do not require user permission or invalidate the unchanged author certificate. Fresh independent completion is authorized with receipt-driven log access. Historical author deviations remain separately unresolved for final acceptance.',
 prospective_resolution='NEW immutable display_receipt.py validates a known completed own runner receipt basename, resolves its recorded own log, verifies both path containment and recorded log hash, and displays a bounded chunk. No guessed log filenames. Guard-rejected typo/absent own artifact is an ordinary recorded failure to correct, not by itself cause to abandon all independent mathematical review; actual protected access/frozen mutation/uncapped substantive execution remains serious.',
 credit=0,accepted_new=55,target_new=60,previous_accepted=39,root_role='Documentary integrity/process orchestration only; no mathematical/compiler execution')
save(parent,adjudication)
L.mkdir();origins={}
def cp(src,rel):
 dst=L/rel;dst.parent.mkdir(parents=True,exist_ok=True);shutil.copyfile(src,dst);assert sha(src)==sha(dst);origins[rel]=dict(path=str(src),sha256=sha(src))
for n in ['bootstrap.py','runner.py','write_lane.py','verify_frozen.py','check.sh','checker.sh','PINS.json','SOURCE-ORDER.json']:cp(R/n,n)
assert 'os.chdir(lane)' in (L/'runner.py').read_text()
(L/'env.sh').write_text((R/'env.sh').read_text())
for n in ['src','build','audit','audit/displays','receipt','logs','tmp','cache','results','output/pdf']:(L/n).mkdir(parents=True,exist_ok=True)
# Reuse selected immutable original/author/ordinary evidence, not recursive historic review trees.
for q in (R/'inputs').rglob('*'):
 if q.is_file():cp(q,'inputs/'+str(q.relative_to(R/'inputs')))
order=json.loads((L/'SOURCE-ORDER.json').read_text())
for mod in order:cp(R/'inputs/author-src'/f'{mod}.lean',f'src/{mod}.lean')
for n in ['FINAL-REVIEW.md','review.json','SHA256-MANIFEST.json','frozen-after.json','bootstrap-receipt.json']:
 cp(R/n,'inputs/incomplete-review-r5/'+n)
for row in recs:
 cp(R/row['path'],'inputs/incomplete-review-r5/'+row['path'])
 j=json.loads((R/row['path']).read_text());rel=str(Path(j['log']).relative_to(R));cp(R/rel,'inputs/incomplete-review-r5/'+rel)
cp(parent,'inputs/root/INCOMPLETE-REVIEW-R5-ADJUDICATION.json')
cp(ROOT/'shoe-review-r5-activity-evidence.json','inputs/root/REVIEW-R5-FAILED-DISPLAY-TOOL-EVIDENCE.json')
display='''import os,resource
os.sched_setaffinity(0,sorted(os.sched_getaffinity(0))[:2])
resource.setrlimit(resource.RLIMIT_CPU,(10,10))
resource.setrlimit(resource.RLIMIT_AS,(536870912,536870912))
from pathlib import Path
import sys,json,re,hashlib,time
lane=Path(__file__).resolve().parent
os.chdir(lane)
rec={'time_ns':time.time_ns(),'argv':sys.argv,'scope':'Standalone receipt-driven own-log display; self caps only, no compiler-runner/group/native-UI telemetry','affinity':sorted(os.sched_getaffinity(0)),'cpu_s':10,'AS_bytes':536870912,'outer_timeout_s':20}
data=b''
try:
 name=sys.argv[1]
 assert re.fullmatch(r'[0-9]+_[A-Za-z0-9_.-]+[.]json',name), 'Pass exact receipt basename from RECEIPT= output, not a log path or a guess'
 rp=(lane/'receipt'/name).resolve();assert rp.parent==lane/'receipt'
 assert rp.stat().st_size<=1048576
 rb=rp.read_bytes();r=json.loads(rb)
 p=Path(r['log']).resolve();assert p.parent==lane/'logs'
 assert r['exit'] is not None and r['group_members_left']==[]
 h=hashlib.sha256()
 with p.open('rb') as f:
  for b in iter(lambda:f.read(65536),b''):h.update(b)
 assert h.hexdigest()==r['log_sha256'], 'Receipt/log hash mismatch'
 offset=int(sys.argv[2]) if len(sys.argv)>2 else 0
 length=int(sys.argv[3]) if len(sys.argv)>3 else 12000
 assert offset>=0 and 0<length<=16384
 with p.open('rb') as f:f.seek(offset);data=f.read(length)
 rec.update(receipt=name,receipt_sha256=hashlib.sha256(rb).hexdigest(),log=str(p),log_sha256=h.hexdigest(),runner_exit=r['exit'],offset=offset,bytes=len(data),exit=0)
except Exception as e:
 rec.update(exit=1,error=type(e).__name__+': '+str(e))
out=lane/'audit/displays'/('receipt-display-'+str(rec['time_ns'])+'.json')
out.write_text(json.dumps(rec,indent=2)+'\\n')
print(json.dumps(rec),flush=True)
if rec['exit']==0:
 sys.stdout.buffer.write(data);sys.stdout.buffer.write(b'\\n');sys.stdout.buffer.flush()
sys.exit(rec['exit'])
'''
(L/'display_receipt.py').write_text(display)
task=(R/'TASK.txt').read_text().replace(str(R),str(L))
start=task.index('Prospective OWN-LOG DISPLAY exception:')
end=task.index('\n\nRead copied literal',start)
task=task[:start]+'''PROSPECTIVE RECEIPT-DRIVEN OWN-LOG DISPLAY: after a runner command returns `RECEIPT=/absolute/own/receipt/TIMESTAMP_LABEL.json EXIT=...`, use `timeout 20 python3 -I -B OWN/display_receipt.py TIMESTAMP_LABEL.json OFFSET [LENGTH<=16384]`. Pass EXACT basename from that return; do not invent a log filename. Helper front-caps affinity2/CPU10/AS512MiB, validates own receipt containment and completion, resolves its recorded own log and SHA, displays only bounded own log bytes, records audit/displays JSON for success OR failure. No log-path arguments, no historical backfill, no compiler/group/native-UI telemetry claim. If ordinary malformed argument/absent own artifact is guard-rejected, retain actual failure, obtain correct known receipt, and continue authorized review; this alone is not protected access or grounds to abandon all work. Actual protected read/frozen mutation/uncapped substantive work remains serious: stop affected activity and disclose without waiver. All source/API reads remain runner-mediated, their known own logs displayed through this helper. Direct view_image of own rendered documentary pages allowed as distinct UI evidence. All new text via write_lane.py RELPATH TEXT stdin; own binary rendering only capped documented generators. No empty Lean/binary/base64 textwriter payload.

ROOT PROCESS RESOLUTION: inputs/root/INCOMPLETE-REVIEW-R5-ADJUDICATION.json records prior review's two guessed log paths rejected before content display; all1596frozen remained unchanged, no compiler ran. Preserve that deviation, do not recast it as full compliance or mathematical rejection. Root authorizes this NEW independent review personally from unchanged author sources; no user approval required. Do not adopt incomplete r5 source-map/pin/ordinary comments as independent proof certification. Your task is to COMPLETE all fresh source/proof/audit/manuscript gates below, not stop merely on a repaired own-lane CLI typo. All older author/r3/r4 deviations and prior-art access limits remain separate pending root acceptance.
'''.replace('OWN',str(L))+task[end:]
task=task.replace('Currentr4 standalone display helper is prospective exact self-capexception;','Authorr4 standalone display helper was its prospective self-capexception;')
task=task.replace('Nochildren/nofallback. Current55/60','Nochildren/nofallback. Current55/60')
(L/'TASK.txt').write_text(task)
save(L/'INPUT-ORIGINS.json',origins)
save(L/'ROOT-PREP.json',dict(utc=now,role='Fresh independent completion after incomplete review, no mathematical repair assumed',mathdb_id=324571,model='gpt-6.1-sol',reasoning='high',service='default',network=False,children=False,protected_peers=['cmdrr-five-three-formal-independent-review-sol-r5','binary-projection-ratio-source-review-sol-r1'],credit=0,campaign=55,previous=39,process_resolution=str(parent)))
bind=dict(frozen)
bind.update({str(R/n):v['sha256'] for n,v in files.items()})
bind[str(R/'SHA256-MANIFEST.json')]=sha(R/'SHA256-MANIFEST.json')
for n in m['exact_terminal_self_exclusions']:bind[str(R/n)]=sha(R/n)
for rel in origins:
 if not rel.startswith('src/'):bind[str(L/rel)]=sha(L/rel)
for n in ['env.sh','display_receipt.py','TASK.txt','INPUT-ORIGINS.json','ROOT-PREP.json']:bind[str(L/n)]=sha(L/n)
save(L/'frozen-inputs.json',bind)
assert all(sha(Path(n))==v for n,v in bind.items())
save(ROOT/'shoe-review-r6-ready.json',dict(utc=now,lane=str(L),target=324571,frozen=len(bind),modules=len(order),task_sha256=sha(L/'TASK.txt'),credit=0,model='gpt-6.1-sol',reasoning='high',service='default'))
print(json.dumps(dict(parent=str(parent),review_manifest=len(files),frozen=len(frozen),receipts=len(recs),new_lane=str(L),new_frozen=len(bind),modules=len(order))))
