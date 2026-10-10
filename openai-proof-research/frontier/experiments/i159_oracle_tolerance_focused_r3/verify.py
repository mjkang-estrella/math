"""Offline read-only evidence replay. No ancestor code or diagnostics are executed."""
import sys,os,json,hashlib
from pathlib import Path
sys.dont_write_bytecode=True
ROOT=Path(__file__).resolve().parents[3]
S=ROOT/'frontier/sources/i159_oracle_tolerance_focused_r3'
E=ROOT/'frontier/experiments/i159_oracle_tolerance_focused_r3'
REPORT=ROOT/'frontier/reviews/i159-oracle-tolerance-focused-r3.md'

def guard(event,args):
 if event=='open':
  mode=args[1];flags=args[2]
  if (isinstance(mode,str) and any(c in mode for c in 'wax+')) or (isinstance(flags,int) and flags&(os.O_WRONLY|os.O_RDWR|os.O_CREAT|os.O_TRUNC|os.O_APPEND)):
   raise RuntimeError('read-only replay denied file mutation')
 if event.startswith(('socket.','subprocess.','ctypes.')) or event in {
  'os.system','os.posix_spawn','os.posix_spawnp','os.fork','os.forkpty','os.exec','os.spawn',
  'os.remove','os.rename','os.rmdir','os.mkdir','os.link','os.symlink','os.truncate','os.chmod','os.chown','os.utime','os.putenv','os.unsetenv','shutil.copyfile','shutil.copymode','shutil.copystat'}:
  raise RuntimeError('read-only replay denied '+event)
sys.addaudithook(guard)
def sha(b):return hashlib.sha256(b).hexdigest()
def read(p):return (ROOT/p).read_bytes()
def obj(p):return json.loads(p.read_text())
def check_record(r):
 b=read(r['path']);assert sha(b)==r['sha256'],r['path']
 if 'bytes' in r:assert len(b)==r['bytes'],r['path']
 return b
seal=obj(S/'seal.json');invbytes=(S/'inventory.json').read_bytes();assert sha(invbytes)==seal['inventory_sha256']
inv=json.loads(invbytes);names=[r['path'] for r in inv];assert names==sorted(set(names))
actual={str(p.relative_to(ROOT)) for d in (S,E) for p in d.rglob('*') if p.is_file()}
actual.add(str(REPORT.relative_to(ROOT)))
assert actual==set(names)|{str((S/'inventory.json').relative_to(ROOT)),str((S/'seal.json').relative_to(ROOT))},'owned inventory drift'
for r in inv:check_record(r)
immutable=obj(S/'immutable.json');assert [r['path'] for r in immutable]==sorted(set(r['path'] for r in immutable))
assert not any('i158' in r['path'].lower() for r in immutable)
for r in immutable:check_record(r)
expected={
 'frontier/iterations/iteration157-dimension-independent-oracle-tolerance-r2-task.json':'b6975be60991316c0d845e3f3e4541f8c3fb66addca871f7d109a5ee423a0940',
 'frontier/iterations/iteration154-dimension-independent-oracle-tolerance-task.json':'0fa43c233f6032d38f3b905cac2253321303e3a300342112ae8716e504897d97',
 'frontier/iterations/iteration152-algorithmic-sampling-reconstruction-discovery-task.json':'f13a8eb19fe9ee8cdd1a6fbeb6618529a48c0599f08a84272be5b68570bf7379',
 'frontier/iterations/i154-dimension-independent-oracle-tolerance.md':'1878b68a5482aba8807f4d910465f83b43d86d401af1a53d038cfebc40b08be1',
 'frontier/reviews/i157-dimension-independent-oracle-tolerance-r2.md':'dc8e9a8142f5b239aa1fb886ed862be745237feed118580f74a31736cb61c2dc'}
for p,h in expected.items():assert sha(read(p))==h,p
snapshots=obj(S/'snapshots.json');assert {r['live_path'] for r in snapshots}=={'README.md','frontier/README.md','frontier/TEN-FINDINGS.md','frontier/iterations/README.md'}
for r in snapshots:assert sha(read(r['snapshot']))==r['sha256']
# Live ledgers are deliberately not read by replay.
ctx=obj(S/'context-coverage.json')
for task in ctx['tasks']:
 j=json.loads(read(task['original']));fields=[]
 def walk(x,path='$'):
  if isinstance(x,dict):
   for k,v in x.items():yield from walk(v,path+'.'+k)
  elif isinstance(x,list):
   for k,v in enumerate(x):yield from walk(v,path+f'[{k}]')
  else:
   fields.append({'path':path,'type':type(x).__name__,'value_sha256':sha(str(x).encode())})
   yield f'FIELD {path}\n{x}\nEND FIELD {path}\n'
 assert ''.join(walk(j))==read(task['decoded']).decode()
 assert fields==task['fields']
 n=task['iteration'];assert obj(S/f'parent{n}-review.json')==json.loads(read(f'frontier/experiments/i{n}-parent-verification.json'))['parent_review']
for r in ctx['embedded_original_occurrences']:
 t=json.loads(read(r['task']))[r['field']][r['start_unicode']:r['end_unicode']]
 assert t==read(r['source']).decode().rstrip();assert sha(t.encode())==r['substring_sha256']
log=obj(S/'read-log.json');coverage={}
for r in log:
 b=read(r['path']);assert sha(b)==r['sha256'];lines=b.decode().splitlines();assert len(lines)==r['total_lines'];assert 1<=r['start']<=r['end']<=len(lines)
 p='\n'.join(lines[r['start']-1:r['end']]);assert sha(p.encode())==r['passage_sha256'];assert lines[r['end']-1]==r['ending']
 coverage.setdefault(r['path'],set()).update(range(r['start'],r['end']+1))
deps=obj(S/'dependencies.json');assert deps['pin']==json.loads(read('sources/upstream.json'))['commit']=='fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb'
tree=json.loads(read('sources/preprints-tree.json'));assert not tree['truncated'];index={r['path']:r for r in tree['tree']}
assert {Path(r['path']).stem for r in deps['sources']}=={'introduction','preliminaries','jets','divergence','centering','numerics','implementation','sampling'}
for r in deps['sources']:
 b=check_record(r);g=hashlib.sha1(b'blob '+str(len(b)).encode()+b'\0'+b).hexdigest();assert g==r['git_blob']==index[r['source_path']]['sha']
 assert coverage[r['path']]>=set(range(1,r['lines']+1)),r['path']
for r in deps['external_proof']['receipts']:
 assert sha(read(r['path']))==r['sha256']
 if 'text_path' in r:assert sha(read(r['text_path']))==r['text_sha256']
primary='frontier/sources/i154_dimension_independent_oracle_tolerance/primary/shifted1.txt'
assert coverage[primary]>=set(range(235,607))
status=obj(S/'review-status.json');assert status['verdict']=='PASS without substantive repairs';assert status['historical_internal_reserve_assertion']=='FAIL';assert status['historical_I157_broad_audit'].startswith('INCOMPLETE');assert status['equations_independently_rebuilt']==list(range(1,20));assert status['unpaid_actual_mathematical_dependencies']==[]
assert json.loads(read('frontier/sources/i157_dimension_independent_oracle_tolerance_r2/review-status.json'))['task_status']=='INCOMPLETE'
assert deps['missing_actual_dependencies']==[];assert ctx['older_recursive_semantic_audit_complete'] is False
assert status['contribution_decision'] is None and status['acceptance_decision'] is None
print(json.dumps({'status':'PASS','mode':'offline read-only','owned_files':len(inv)+2,'immutable_files':len(immutable),'complete_new_source_files':len(deps['sources']),'new_passage_receipts':len(log),'decoded_fields':sum(len(t['fields']) for t in ctx['tasks']),'embedded_original_occurrences':len(ctx['embedded_original_occurrences']),'original_R154_review_verdict':status['verdict'],'historical_I157_broad_audit':status['historical_I157_broad_audit'],'historical_internal_reserve_assertion':'FAIL','ancestor_programs_executed':0,'finite_numerical_diagnostics':0,'writes_network_subprocess_bytecode':'denied','seal_sha256':sha((S/'seal.json').read_bytes()),'scope':'Evidence consistency only. Universal proof judgment is in the review; no contribution or acceptance certification.'},indent=2))
