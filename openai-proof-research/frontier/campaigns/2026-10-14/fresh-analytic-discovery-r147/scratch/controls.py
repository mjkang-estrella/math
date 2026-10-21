from pathlib import Path
import hashlib,json,subprocess,os
R=Path('frontier/campaigns/2026-10-14/fresh-analytic-discovery-r147');F=R/'private/controls/fixture';F.mkdir(parents=True,exist_ok=True)
for src,dest in [('GAPS.md','GAPS.md'),('verify.py','verify.py')]: (F/dest).write_bytes((R/src).read_bytes())
(F/'FINAL.md').write_text('Fresh selected-copy control fixture; not an original archive seal.\n')
(F/'REPORT.md').write_text('Only copied GAPS.md and verifier are payload members. No mathematics certified.\n')
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
rows=[{'path':n,'size':(F/n).stat().st_size,'sha256':sha(F/n)} for n in ['GAPS.md','verify.py']]
(F/'MANIFEST.json').write_text(json.dumps({'excluded_envelopes':['FINAL.md','MANIFEST.json','REPORT.md'],'files':rows},indent=2)+'\n')
anchors={n:sha(F/n) for n in ['FINAL.md','MANIFEST.json','REPORT.md']}
def snapshot():return {str(p.relative_to(F)):sha(p) for p in sorted(F.rglob('*')) if p.is_file()}
results=[]
def run(label,expected,wrong=False):
 before=snapshot();cmd=['python',str(F/'verify.py'),str(F),'--final-sha256',anchors['FINAL.md'],'--manifest-sha256','0'*64 if wrong else anchors['MANIFEST.json'],'--report-sha256',anchors['REPORT.md']]
 r=subprocess.run(cmd,cwd=Path.cwd(),env={**os.environ,'PYTHONDONTWRITEBYTECODE':'1'},capture_output=True,text=True,timeout=20)
 assert snapshot()==before,'verifier mutated fixture'
 assert (r.returncode==0)==expected,(label,r.stderr)
 results.append({'control':label,'expected_accept':expected,'accepted':r.returncode==0,'read_only_snapshot_match':True})
run('baseline',True);orig=(F/'GAPS.md').read_bytes()
(F/'GAPS.md').write_bytes(orig+b'changed\n');run('changed payload',False);(F/'GAPS.md').write_bytes(orig)
(F/'GAPS.md').unlink();run('missing payload',False);(F/'GAPS.md').write_bytes(orig)
(F/'.extra').write_text('extra');run('hidden extra',False);(F/'.extra').unlink()
run('wrong detached manifest anchor',False,True);run('restored',True)
(R/'CONTROL-RESULTS.json').write_text(json.dumps({'selection':'fresh2-file selection; no inherited original manifest','anchors':anchors,'controls':results},indent=2)+'\n')
print('6 copied controls; all verifier invocations left each current fixture unchanged')
