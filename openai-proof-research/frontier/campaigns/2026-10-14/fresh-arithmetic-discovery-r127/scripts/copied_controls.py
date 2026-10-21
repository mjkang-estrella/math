from pathlib import Path
import hashlib,json,subprocess,shutil,importlib.util
r=Path('frontier/campaigns/2026-10-14/fresh-arithmetic-discovery-r127');fixture=r/'private/copied-control';fixture.mkdir(exist_ok=False)
shutil.copyfile(r/'verify.py',fixture/'verify.py');shutil.copyfile(r/'notes/integrated-threshold-reduction.md',fixture/'note.md')
spec=importlib.util.spec_from_file_location('verify',r/'verify.py');v=importlib.util.module_from_spec(spec);spec.loader.exec_module(v)
(fixture/'MANIFEST.json').write_text(json.dumps(v.inventory(fixture),indent=2)+'\n')
(fixture/'FINAL.md').write_text('Copied two-file artifact fixture, not an original source packet.\n')
(fixture/'REPORT.md').write_text('Own exact manifest; original root untouched. Artifact checks only.\n')
anchors={x:hashlib.sha256((fixture/x).read_bytes()).hexdigest() for x in v.ENVELOPES}
def snap():
 return {p.relative_to(fixture).as_posix():('directory' if p.is_dir() else hashlib.sha256(p.read_bytes()).hexdigest()) for p in fixture.rglob('*')}
rows=[]
def check(name,expected,replace=None):
 a=dict(anchors);a.update(replace or {});before=snap()
 args=['python','-B',str(r/'verify.py'),'--root',str(fixture),'--final-sha256',a['FINAL.md'],'--manifest-sha256',a['MANIFEST.json'],'--report-sha256',a['REPORT.md']]
 z=subprocess.run(args,capture_output=True,text=True,timeout=15);unchanged=before==snap()
 rows.append(dict(name=name,expected_success=expected,success=z.returncode==0,readonly_content=unchanged,output=(z.stdout+z.stderr).strip()))
 assert (z.returncode==0)==expected and unchanged
check('baseline',True)
p=fixture/'note.md';b=p.read_bytes();p.write_bytes(b+b'changed\n');check('changed payload',False);p.write_bytes(b)
p.unlink();check('missing payload',False);p.write_bytes(b)
p=fixture/'.extra';p.write_text('extra');check('hidden extra file',False);p.unlink()
p=fixture/'extra-empty';p.mkdir();check('extra empty directory',False);p.rmdir()
check('wrong manifest anchor',False,{'MANIFEST.json':'0'*64})
p=fixture/'REPORT.md';b=p.read_bytes();p.write_bytes(b+b'changed\n');check('changed outside report',False);p.write_bytes(b)
check('restored baseline',True)
(r/'private/copied-controls-results.json').write_text(json.dumps({'fixture_originals':['verify.py','notes/integrated-threshold-reduction.md'],'own_anchors':anchors,'checks':rows,'limits':'content/membership snapshots only; no permission/timestamp or concurrent-writer claim'},indent=2)+'\n')
print('Eight copied artifact controls behaved as expected; verifier did not change fixture content.')
