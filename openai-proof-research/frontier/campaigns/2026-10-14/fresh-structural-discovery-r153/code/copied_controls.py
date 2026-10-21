# Original r153, MIT. Only writes a tiny fresh selection fixture under own root.
import hashlib,json,os,shutil,stat,subprocess
from pathlib import Path
ROOT=Path.cwd();assert str(ROOT)=='/home/mj-kang/Documents/Dev/math/openai-proof-research'
OWN=ROOT/'frontier/campaigns/2026-10-14/fresh-structural-discovery-r153'
FIX=OWN/'private/controls/selection';FIX.mkdir(parents=True,exist_ok=False)
sha=lambda b:hashlib.sha256(b).hexdigest()
sources=['notes/01-prefreeze-calculations.md','code/verify_packet.py']
selection=[]
for src in sources:
 b=(OWN/src).read_bytes();dst=FIX/Path(src).name;dst.write_bytes(b)
 selection.append({'source':src,'selected_copy':dst.relative_to(OWN).as_posix(),'bytes':len(b),'sha256':sha(b)})
(FIX/'FINAL.md').write_text('Fresh two-file copied-control selection. No inherited membership.\n')
(FIX/'REPORT.md').write_text('Artifact controls only; no mathematical gate.\n')
files=[{'path':Path(s).name,'bytes':len((OWN/s).read_bytes()),'sha256':sha((OWN/s).read_bytes())} for s in sources]
(FIX/'MANIFEST.json').write_text(json.dumps({'schema':'r153-exact-v1','directories':['.'],'files':sorted(files,key=lambda x:x['path'])},indent=2)+'\n')
anchors={n:sha((FIX/n).read_bytes()) for n in ['FINAL.md','MANIFEST.json','REPORT.md']}
def snap():
 result=[]
 for base,ds,fs in os.walk(FIX):
  for name in sorted(ds+fs):
   p=Path(base)/name;st=p.lstat();result.append((p.relative_to(FIX).as_posix(),stat.S_IMODE(st.st_mode),st.st_nlink,p.is_dir(),sha(p.read_bytes()) if p.is_file() else None))
 return sorted(result)
results=[]
def check(label,expect,custom=None):
 before=snap();a=custom or anchors
 cmd=['python',str(FIX/'verify_packet.py'),str(FIX),'--final',a['FINAL.md'],'--manifest',a['MANIFEST.json'],'--report',a['REPORT.md']]
 p=subprocess.run(cmd,capture_output=True,text=True,timeout=10);after=snap()
 assert before==after
 assert (p.returncode==0)==expect,(label,p.stdout,p.stderr)
 results.append({'label':label,'accepted':p.returncode==0,'read_only_snapshot_equal':True,'output':(p.stdout+p.stderr).strip()})
check('baseline',True)
p=FIX/'01-prefreeze-calculations.md';original=p.read_bytes();p.write_bytes(original+b'changed\n');check('changed payload',False);p.write_bytes(original)
p.rename(FIX/'missing.tmp');check('missing payload',False);(FIX/'missing.tmp').rename(p)
(FIX/'.extra').write_text('x');check('hidden extra',False);(FIX/'.extra').unlink()
(FIX/'empty').mkdir();check('empty extra directory',False);(FIX/'empty').rmdir()
a=dict(anchors);a['MANIFEST.json']='0'*64;check('wrong detached manifest',False,a)
p=FIX/'REPORT.md';old=p.read_bytes();p.write_bytes(old+b'x');check('changed outside REPORT',False);p.write_bytes(old)
check('restored',True)
independent=subprocess.run(['sha256sum',str(FIX/'FINAL.md'),str(FIX/'MANIFEST.json'),str(FIX/'REPORT.md')],capture_output=True,text=True,timeout=10)
for line in independent.stdout.splitlines():digest,name=line.split(maxsplit=1);assert anchors[Path(name).name]==digest
for item in selection:assert sha((OWN/item['source']).read_bytes())==item['sha256']
(OWN/'private/controls/results.json').write_text(json.dumps({'selection':selection,'anchors':anchors,'checks':results,'sha256sum':independent.stdout,'originals_unchanged':True},indent=2)+'\n')
print('Eight copied-selection integrity checks passed; all verifier runs read-only; source files unchanged.')
