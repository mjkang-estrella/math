"""Preparation only: writes exclusively to this packet's private/controls.
Reduced copies get new manifests. Never certifies a reduced copy by an original manifest.
"""
from pathlib import Path
import hashlib,json,os,shutil,subprocess,sys
R=Path(__file__).resolve().parents[2];P=R/'packet';C=P/'private/controls';C.mkdir(exist_ok=False)
def h(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def listing(p):return {f.relative_to(p).as_posix():h(f) for f in p.rglob('*') if f.is_file()}
old=listing(P);F=C/'fixture';(F/'packet/scripts').mkdir(parents=True)
for a,b in [('scripts/verify.py','scripts/verify.py'),('notes/donovan-feasibility.md','research-copy.md')]:shutil.copyfile(P/a,F/'packet'/b)
fp=F/'packet';files=[{'path':n,'size':(fp/n).stat().st_size,'sha256':v} for n,v in sorted(listing(fp).items())]
m={'schema':'r111-payload-v1','purpose':'new reduced-copy membership only; not original authentication','directories':['scripts'],'files':files}
(fp/'manifest.json').write_text(json.dumps(m,indent=2)+'\n')
(F/'REPORT.md').write_text('Reduced-copy artifact fixture only. No mathematical gate.\n')
om={'schema':'r111-outside-v1','packet_manifest_sha256':h(fp/'manifest.json'),'report_sha256':h(F/'REPORT.md')};(F/'MANIFEST.json').write_text(json.dumps(om,indent=2)+'\n')
fin={'status':'reduced-copy-control','manifest_sha256':h(F/'MANIFEST.json'),'report_sha256':h(F/'REPORT.md'),'packet_manifest_sha256':h(fp/'manifest.json'),'payload_count':len(files)};(F/'FINAL.json').write_text(json.dumps(fin,indent=2)+'\n')
anchors={x:h(F/(x+'.json' if x!='REPORT' else 'REPORT.md')) for x in ['FINAL','MANIFEST','REPORT']}
base=[sys.executable,'-B',str(fp/'scripts/verify.py'),'--root',str(F),'--final-sha256',anchors['FINAL'],'--manifest-sha256',anchors['MANIFEST'],'--report-sha256',anchors['REPORT'],'--integrity-only']
results=[]
def check(name,accepted,cmd=base):
 before=listing(F);s=subprocess.run(cmd,capture_output=True,text=True);after=listing(F)
 assert before==after,'verifier wrote fixture';assert (s.returncode==0)==accepted,(name,s.stdout,s.stderr)
 results.append({'case':name,'expected_acceptance':accepted,'exit':s.returncode,'read_only':True,'result':json.loads(s.stdout)})
check('clean reduced copy',True)
f=fp/'research-copy.md';b=f.read_bytes();f.write_bytes(b+b'changed\n');check('changed payload',False);f.write_bytes(b)
f.unlink();check('missing payload',False);f.write_bytes(b)
e=fp/'.unexpected-hidden';e.write_text('extra');check('extra hidden payload',False);e.unlink()
wrong=base.copy();wrong[wrong.index('--final-sha256')+1]='0'*64;check('wrong external anchor',False,wrong)
check('restored reduced copy',True)
assert all(h(P/n)==v for n,v in old.items()),'original packet input changed'
(C/'results.json').write_text(json.dumps({'scope':'copied artifact controls only; original incoming authentication is separate','fixture_anchors':anchors,'original_input_files_unchanged':len(old),'cases':results},indent=2)+'\n')
print(json.dumps({'cases':len(results),'all_expected':True,'original_input_files_unchanged':len(old)}))
