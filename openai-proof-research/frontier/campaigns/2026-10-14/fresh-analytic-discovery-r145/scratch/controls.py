from pathlib import Path
import hashlib,json,subprocess,sys
R=Path('frontier/campaigns/2026-10-14/fresh-analytic-discovery-r145').absolute();F=R/'private/control-fixture';F.mkdir(parents=True,exist_ok=False)
def sh(b):return hashlib.sha256(b).hexdigest()
b=(R/'GAPS.md').read_bytes();(F/'selected-prose.md').write_bytes(b)
(F/'FINAL.md').write_text('Disposable selected-prose integrity fixture, not a research nomination.\n');(F/'REPORT.md').write_text('Membership independently enumerated for this single copied file.\n')
(F/'MANIFEST.json').write_text(json.dumps({'files':[{'path':'selected-prose.md','size':len(b),'sha256':sh(b)}]},indent=2)+'\n')
anchors={n:sh((F/n).read_bytes()) for n in ['FINAL.md','MANIFEST.json','REPORT.md']}
def snap():return {q.relative_to(F).as_posix():sh(q.read_bytes()) for q in F.rglob('*') if q.is_file()}
rows=[]
def check(name,good,wrong=False):
 before=snap();cmd=[sys.executable,str(R/'verify.py'),'--root',str(F),'--final-sha256',anchors['FINAL.md'],'--manifest-sha256',('0'*64 if wrong else anchors['MANIFEST.json']),'--report-sha256',anchors['REPORT.md']];v=subprocess.run(cmd,capture_output=True,text=True);after=snap();assert before==after;assert (v.returncode==0)==good;rows.append({'case':name,'expected_accept':good,'returncode':v.returncode,'unchanged_by_verifier':True,'result':v.stdout.strip() or v.stderr.strip()})
check('baseline',True);(F/'selected-prose.md').write_bytes(b+b'X');check('altered payload',False);(F/'selected-prose.md').unlink();check('missing payload',False);(F/'selected-prose.md').write_bytes(b);(F/'.extra').write_text('extra');check('hidden extra',False);(F/'.extra').unlink();check('wrong detached manifest anchor',False,True);check('restored baseline',True)
(R/'CONTROLS.json').write_text(json.dumps({'note':'Six copied-selection byte controls, not mathematical gates. No source body or original manifest copied.','cases':rows,'fixture_anchors':anchors},indent=2)+'\n');print('Six expected outcomes; every verifier call left fixture bytes unchanged.')
