"""Small copied artifact controls; no mathematics is gated by these tests."""
from pathlib import Path
import hashlib,json,os,stat,subprocess,sys
R=Path('frontier/campaigns/2026-10-14/fresh-structural-discovery-r154')
F=R/'seal/copied-controls'
if F.exists(): raise SystemExit('refuse to rebuild existing controls')
F.mkdir()
for src,dst in [('original/verify.py','verify.py'),('notes/01-prefreeze-calculations.md','note.md')]:
 (F/dst).write_bytes((R/src).read_bytes())
ns={'__name__':'readonly_helpers'}
exec(compile((R/'original/verify.py').read_text(),str(R/'original/verify.py'),'exec'),ns)
(F/'FINAL.md').write_text('Copied artifact fixture only; not a mathematical gate.\n')
(F/'REPORT.md').write_text('Two copied original files; original files unchanged.\n')
(F/'MANIFEST.json').write_text(json.dumps(ns['inventory'](F),indent=2,sort_keys=True)+'\n')
hashout=subprocess.run(['sha256sum',str(F/'FINAL.md'),str(F/'MANIFEST.json'),str(F/'REPORT.md')],capture_output=True,text=True,check=True).stdout
anchors=[line.split()[0] for line in hashout.splitlines()]
def snapshot():
 out={}
 for base,ds,fs in os.walk(F):
  for name in ['.'] if Path(base)==F else []:
   p=Path(base);s=p.lstat();out['.']={'mode':stat.S_IMODE(s.st_mode),'links':s.st_nlink,'kind':'dir'}
  for name in ds+fs:
   p=Path(base)/name;s=p.lstat();rel=p.relative_to(F).as_posix()
   out[rel]={'mode':stat.S_IMODE(s.st_mode),'links':s.st_nlink,'kind':'dir' if p.is_dir() else 'file','sha256':hashlib.sha256(p.read_bytes()).hexdigest() if p.is_file() else None}
 return out
records=[]
def check(label,accepted,override=None):
 a=anchors if override is None else override
 cmd=[sys.executable,str(F/'verify.py'),str(F),'--final',a[0],'--manifest',a[1],'--report',a[2]]
 before=snapshot();p=subprocess.run(cmd,capture_output=True,text=True,timeout=10);after=snapshot()
 assert (p.returncode==0)==accepted,(label,p.stdout,p.stderr)
 assert before==after,label+' verifier mutation'
 records.append({'case':label,'expected_accept':accepted,'returncode':p.returncode,'readonly_snapshot_equal':True,'stdout':p.stdout.strip(),'stderr':p.stderr.strip()})
check('baseline',True)
original=(F/'note.md').read_bytes();(F/'note.md').write_bytes(original+b'alteration\n');check('changed-payload',False);(F/'note.md').write_bytes(original)
(F/'note.md').unlink();check('missing-payload',False);(F/'note.md').write_bytes(original)
(F/'.extra').write_text('extra');check('hidden-extra',False);(F/'.extra').unlink()
(F/'empty-extra').mkdir();check('empty-directory-extra',False);(F/'empty-extra').rmdir()
check('wrong-manifest-anchor',False,[anchors[0],'0'*64,anchors[2]])
report=(F/'REPORT.md').read_bytes();(F/'REPORT.md').write_bytes(report+b'change');check('changed-outside-report',False);(F/'REPORT.md').write_bytes(report)
check('restored',True)
assert (R/'original/verify.py').read_bytes()==(F/'verify.py').read_bytes()
assert (R/'notes/01-prefreeze-calculations.md').read_bytes()==(F/'note.md').read_bytes()
(R/'private/controls-receipt.json').write_text(json.dumps({'mathematical_gate':False,'independent_sha256sum':hashout,'cases':records,'original_copy_sources_unchanged':True},indent=2)+'\n')
print(json.dumps({'copied_controls':len(records),'expected_outcomes_observed':True,'readonly':True,'mathematical_gate':False}))
