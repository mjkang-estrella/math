"""Proportionate reduced-copy controls; originals are read-only."""
import hashlib,json,os,shutil,stat,subprocess,sys
from pathlib import Path
sys.dont_write_bytecode=True
from seal import seal
R=Path('frontier/campaigns/2026-10-14/fresh-arithmetic-discovery-r124');C=R/'private/copied-controls';C.mkdir();(C/'selected').mkdir()
sources=[R/'private/pinned/04-norm-tori.tex',R/'notes/integrated-norm-reduction.md']
def digest(p):return hashlib.sha256(p.read_bytes()).hexdigest()
originals={str(p):digest(p) for p in sources}
for p in sources:shutil.copyfile(p,C/'selected'/p.name)
(C/'FINAL.md').write_text('Reduced artifact control only; two selected files. No original manifest inherited. No mathematical gate.\n')
(C/'REPORT.md').write_text('Own exact membership; protected selected source remains private/local under original rights.\n')
anchors=seal(C)
def snap():
 out={}
 for p in [C]+sorted(C.rglob('*')):
  s=p.lstat();out[str(p.relative_to(C))]={'mode':stat.S_IMODE(s.st_mode),'links':s.st_nlink,'kind':'dir' if p.is_dir() else 'file','sha256':digest(p) if p.is_file() else None}
 return out
baseline=snap();tests=[]
def run(name,ok,override=None):
 a=anchors.copy();a.update(override or {})
 cmd=[sys.executable,str(R/'verify.py'),str(C),'--final-sha256',a['FINAL.md'],'--manifest-sha256',a['MANIFEST.json'],'--report-sha256',a['REPORT.md']]
 before=snap();res=subprocess.run(cmd,capture_output=True,text=True,timeout=15);after=snap()
 assert before==after,'verifier modified control'
 assert (res.returncode==0)==ok,(name,res.stdout,res.stderr)
 tests.append({'case':name,'expected_accept':ok,'returncode':res.returncode,'read_only_snapshot_equal':True,'output':(res.stdout+res.stderr).strip()})
run('baseline',True)
p=C/'selected'/sources[0].name;b=p.read_bytes();p.write_bytes(b+b'\ncontrol mutation\n');run('changed-payload',False);p.write_bytes(b)
p.unlink();run('missing-payload',False);p.write_bytes(b)
p=C/'.hidden-extra';p.write_bytes(b'x');run('hidden-extra',False);p.unlink()
p=C/'extra-empty';p.mkdir();run('empty-extra-directory',False);p.rmdir()
run('wrong-detached-manifest',False,{'MANIFEST.json':'0'*64})
run('restoration',True)
assert baseline==snap()
assert originals=={str(p):digest(p) for p in sources}
(R/'private/copied-controls-results.json').write_text(json.dumps({'fixture':str(C),'independent_detached_anchors':anchors,'selected_original_hashes':originals,'originals_unchanged':True,'restoration_exact':True,'tests':tests,'mathematical_gate':False},indent=2)+'\n')
print('Seven copied controls behaved as expected; each verifier call read-only; selected originals unchanged.')
