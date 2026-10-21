"""Proportionate selected-copy integrity controls; never mutates an original."""
from pathlib import Path
import hashlib,json,os,stat,subprocess,shutil
R=Path('frontier/campaigns/2026-10-14/fresh-structural-discovery-r161')
T=R/'private/copied-control';T.mkdir()
for n in ['scope-frozen.md','author-proof.md']:shutil.copy2(R/n,T/n)
(T/'FINAL.md').write_text('Selected-copy artifact control, not the original root or a mathematical finding.\n')
(T/'REPORT.md').write_text('Two copied original prose files. Own manifest; no inherited original archive manifest.\n')
def digest(p):return hashlib.sha256(p.read_bytes()).hexdigest()
manifest={'schema':'r161-exact-payload-v1','directories':[],'files':{n:{'size':(T/n).stat().st_size,'sha256':digest(T/n)} for n in ['author-proof.md','scope-frozen.md']}}
(T/'MANIFEST.json').write_text(json.dumps(manifest,indent=2)+'\n')
anchors=[digest(T/n) for n in ['FINAL.md','MANIFEST.json','REPORT.md']]
def snap():
    return {p.name:[digest(p),stat.S_IMODE(p.stat().st_mode),p.stat().st_nlink,p.stat().st_mtime_ns] for p in T.iterdir()}
checks=[]
def check(name,expected,aa=None):
    before=snap();proc=subprocess.run(['python',str(R/'tools/verify.py'),str(T),*(aa or anchors)],capture_output=True,text=True,env=dict(os.environ,PYTHONDONTWRITEBYTECODE='1'));after=snap()
    assert proc.returncode==expected and before==after,(name,proc.stdout,proc.stderr)
    checks.append({'control':name,'expected_exit':expected,'actual_exit':proc.returncode,'read_only_snapshot_equal':True,'message':proc.stdout.strip()})
check('baseline',0)
f=T/'author-proof.md';original=f.read_bytes();meta=f.stat();f.write_bytes(original+b'\nTAMPER\n');check('changed copied payload',1);f.write_bytes(original);os.utime(f,ns=(meta.st_atime_ns,meta.st_mtime_ns))
extra=T/'.unexpected';extra.write_text('hidden extra\n');check('hidden copied extra',1);extra.unlink()
wrong=anchors.copy();wrong[1]='0'*64;check('wrong detached manifest anchor',1,wrong)
check('restored selected copy',0)
(R/'private/copied-control-results.json').write_text(json.dumps({'selection_only':True,'anchor_order':['FINAL','MANIFEST','REPORT'],'anchors':anchors,'checks':checks,'snapshot_fields':['sha256','mode','nlink','mtime_ns'],'limits':'No atime binding; controls are artifact checks, not mathematical gates.'},indent=2)+'\n')
print('Five selected-copy controls behaved as expected; each verifier invocation preserved its target snapshot.')
