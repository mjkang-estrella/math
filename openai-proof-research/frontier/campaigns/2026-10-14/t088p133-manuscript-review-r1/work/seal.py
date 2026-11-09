# Copyright2026 Myeongjin Kang. MIT.
from pathlib import Path
import json,hashlib,stat,datetime
R=Path(__file__).resolve().parents[1];P=R/'packet';h=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
files={};dirs={'packet':{'mode':0o755}}
for p in sorted(P.rglob('*')):
 assert not p.is_symlink()
 if p.is_dir():p.chmod(0o755);dirs[p.relative_to(R).as_posix()]={'mode':0o755}
 elif p.name!='MANIFEST.json' or p.parent!=P:
  p.chmod(0o444);s=p.stat();assert s.st_nlink==1;files[p.relative_to(R).as_posix()]={'bytes':s.st_size,'mode':0o444,'sha256':h(p)}
m=P/'MANIFEST.json';m.write_text(json.dumps({'schema':'T088P133-manuscript-review-r1-exact-v1','files':files,'directories':dirs,'exclusions':['outside work/evidence/renders/tmp copies','private/generic software and engine/cache/compiled dependencies'],'scope':'independent full final manuscript review;no acceptance/count/release'},indent=2,sort_keys=True)+'\n');m.chmod(0o444)
report=R/'REPORT.md';report.chmod(0o444)
f={'candidate':'T088P133','round':'manuscript-review-r1','verdict':'PASS_FULL_MANUSCRIPT_T088P133','required_revisions':[],'optional_suggestions':['Bibliography compaction only;page20 harmless'],'reviewed_r2_FINAL_sha256':'7a98b6fc2f55ddc21187b77dac24538e193492732e36fe0f07fe4c5bf3c29672','manifest_sha256':h(m),'report_sha256':h(report),'public_files':len(files),'public_directories':len(dirs),'full_scope_unchanged':True,'all20pages_individually_inspected':True,'formal_declarations_reproduced':56,'sparse_coefficients_independently_matched':248,'full_theorem_formalized':False,'acceptance_assigned':False,'count_decision_assigned':False,'release_gate_assigned':False,'publication':'STOPPED','operational_deviation':'Initial broad filename traversal,disclosed in limits.md;no excluded active body used','sealed_at_utc':datetime.datetime.now(datetime.timezone.utc).isoformat()}
final=R/'FINAL.json';final.write_text(json.dumps(f,indent=2,sort_keys=True)+'\n');final.chmod(0o444)
a={'FINAL.json':h(final),'packet/MANIFEST.json':h(m),'REPORT.md':h(report),'verifier_sha256':h(R/'packet/public/verify.py')}
(R/'DETACHED-ANCHORS.json').write_text(json.dumps(a,indent=2)+'\n');print(json.dumps(a,indent=2));print('public files',len(files),'directories',len(dirs))
