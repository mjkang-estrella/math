"""Proportionate disposable selection, independently manifested; no inherited manifest."""
from pathlib import Path
import hashlib,json,subprocess,shutil,os
R=Path('frontier/campaigns/2026-10-14/fresh-arithmetic-discovery-r117'); F=R/'packet/private/control-selection'
assert not F.exists();(F/'packet').mkdir(parents=True)
selected=['packet/code/verify.py','packet/notes/feasibility.md','packet/source-identities.json']
for s in selected:shutil.copyfile(R/s,F/'packet'/Path(s).name)
def H(p):b=p.read_bytes();return {'size':len(b),'sha256':hashlib.sha256(b).hexdigest()}
(F/'FINAL.md').write_text('Disposable three-file r117 selection, not the original research root.\n')
(F/'REPORT.md').write_text('Artifact controls only. Own membership; no inherited original manifest.\n')
m={'format':'r117-exact-v1','payload_files':{str(p.relative_to(F)):H(p) for p in sorted((F/'packet').iterdir())},'envelopes':{n:H(F/n) for n in ['FINAL.md','REPORT.md']},'directories':['packet']}
(F/'MANIFEST.json').write_text(json.dumps(m,sort_keys=True,indent=2)+'\n')
anchors={n:H(F/n)['sha256'] for n in ['FINAL.md','MANIFEST.json','REPORT.md']}
def snap():
 out={}
 for d,ds,fs in os.walk(F):
  for n in sorted(ds+fs):
   p=Path(d)/n;s=p.lstat();out[str(p.relative_to(F))]=[s.st_mode,s.st_nlink,H(p) if p.is_file() else None]
 return out
rows=[]
def check(name,expected,wrong=False):
 a=dict(anchors)
 if wrong:a['MANIFEST.json']='0'*64
 before=snap();z=subprocess.run(['python',str(F/'packet/verify.py'),str(F),'--final-sha256',a['FINAL.md'],'--manifest-sha256',a['MANIFEST.json'],'--report-sha256',a['REPORT.md']],capture_output=True,text=True);after=snap()
 row={'case':name,'expected_accept':expected,'accepted':z.returncode==0,'read_only':before==after,'output':z.stdout.strip()};assert row['accepted']==expected and row['read_only'],row;rows.append(row)
check('baseline',True)
p=F/'packet/feasibility.md';b=p.read_bytes();p.write_bytes(b+b'altered\n');check('altered-payload',False);p.write_bytes(b)
p.unlink();check('missing-payload',False);p.write_bytes(b)
p=F/'packet/.extra';p.write_text('extra');check('hidden-extra',False);p.unlink()
p=F/'empty-extra';p.mkdir();check('empty-extra-directory',False);p.rmdir()
check('wrong-detached-anchor',False,True);check('restored',True)
(R/'packet/artifact-controls.json').write_text(json.dumps({'selected_originals':selected,'own_selection_anchors':anchors,'cases':rows,'not_a_math_gate':True},indent=2)+'\n');print(json.dumps(rows,indent=2))
