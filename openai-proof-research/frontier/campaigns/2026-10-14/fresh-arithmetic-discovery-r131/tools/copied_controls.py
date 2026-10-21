"""One small copied packet; reversible tampering only in the copy. Run before main seal."""
from pathlib import Path
import json,hashlib,subprocess,shutil,os
R=Path('frontier/campaigns/2026-10-14/fresh-arithmetic-discovery-r131');r=R/'controls/baseline'
assert not r.exists(),'controls already created'
for d in ['notes','tools','envelopes']:(r/d).mkdir(parents=True,exist_ok=True)
for rel in ['notes/reduction-boundary.md','tools/verify.py']:shutil.copyfile(R/rel,r/rel)
(r/'envelopes/FINAL.md').write_text('Copied control packet, not a research conclusion.\n')
(r/'envelopes/REPORT.md').write_text('Controls test the exact copied boundary note and verifier.\n')
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
env=['envelopes/FINAL.md','envelopes/MANIFEST.json','envelopes/REPORT.md'];files={};dirs=[]
for base,ds,fs in os.walk(r):
 dirs.extend((Path(base)/d).relative_to(r).as_posix() for d in ds)
 for f in fs:
  p=Path(base)/f;rel=p.relative_to(r).as_posix()
  if rel not in env:files[rel]={'size':p.stat().st_size,'sha256':sha(p)}
(r/env[1]).write_text(json.dumps({'schema':1,'directories':sorted(dirs),'files':files},indent=2,sort_keys=True)+'\n')
anchors=[sha(r/x) for x in env];results=[]
def run(name,expect,hs=None):
 cmd=['python','-B',str(r/'tools/verify.py'),str(r),*(hs or anchors)]
 c=subprocess.run(cmd,capture_output=True,text=True);good=(c.returncode==0)
 results.append({'case':name,'expected_acceptance':expect,'observed_acceptance':good,'stdout':c.stdout.strip(),'stderr':c.stderr.strip()});assert good==expect,(name,c.stdout,c.stderr)
run('exact copied baseline',True)
p=r/'notes/reduction-boundary.md';b=p.read_bytes();p.write_bytes(b+b'changed\n');run('payload byte change',False);p.write_bytes(b)
p=r/'unexpected.txt';p.write_text('unexpected\n');run('extra payload member',False);p.unlink()
wrong=anchors.copy();wrong[1]='0'*64;run('wrong detached manifest anchor',False,wrong)
p=r/'envelopes/REPORT.md';b=p.read_bytes();p.write_bytes(b+b'changed\n');run('report envelope byte change',False);p.write_bytes(b)
run('restored copied baseline',True)
(R/'notes/artifact-controls.json').write_text(json.dumps({'scope':'Only a small copy of own boundary note and own verifier; not a mathematical gate. Original payload sources never mutated.','anchors':dict(zip(env,anchors)),'results':results},indent=2)+'\n')
print('Copied controls:',len(results),'expected outcomes; original note/verifier copies match:',all((r/x).read_bytes()==(R/x).read_bytes() for x in files))
