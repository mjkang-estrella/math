"""Small copied controls, performed before the one original packet seal."""
from pathlib import Path
import hashlib,json,os,subprocess,sys
R=Path(__file__).resolve().parent;F=R/'private/controls/packet';F.mkdir(parents=True,exist_ok=True)
def sha(b):return hashlib.sha256(b).hexdigest()
def inv(root,exclude=()):
 files={};dirs=[]
 for h,ds,fs in os.walk(root):
  dirs.extend((Path(h)/n).relative_to(root).as_posix() for n in ds)
  for n in fs:
   p=Path(h)/n;rel=p.relative_to(root).as_posix()
   if rel not in exclude:
    b=p.read_bytes();files[rel]={'size':len(b),'sha256':sha(b)}
 return {'files':dict(sorted(files.items())),'directories':sorted(dirs)}
(F/'data').mkdir(exist_ok=True)
for src,dest in [('DERIVATION.md',F/'data/DERIVATION.md'),('verify.py',F/'verify.py')]:dest.write_bytes((R/src).read_bytes())
outer=['FINAL.md','MANIFEST.json','REPORT.md']
(F/'MANIFEST.json').write_text(json.dumps({'schema':'r139-exact-payload-v1','excluded_root_envelopes':outer,'inventory':inv(F,outer)},sort_keys=True,indent=2)+'\n')
m=sha((F/'MANIFEST.json').read_bytes());(F/'REPORT.md').write_text('Synthetic copied control; manifest '+m+'\n');r=sha((F/'REPORT.md').read_bytes());(F/'FINAL.md').write_text('Synthetic copied control; manifest '+m+' report '+r+'\n');f=sha((F/'FINAL.md').read_bytes())
base=(F/'data/DERIVATION.md').read_bytes();results=[]
def run(name,expected,ms=m):
 before=inv(F)
 env=dict(os.environ,PYTHONDONTWRITEBYTECODE='1',TMPDIR=str(R/'work'))
 p=subprocess.run([sys.executable,str(R/'verify.py'),'--root',str(F),'--manifest-sha',ms,'--report-sha',r,'--final-sha',f],capture_output=True,text=True,env=env,cwd=R)
 after=inv(F);ok=(p.returncode==0)==expected and before==after
 results.append({'case':name,'expected_success':expected,'exit_code':p.returncode,'read_only_observed':before==after,'satisfied':ok,'stdout':p.stdout,'stderr':p.stderr})
 assert ok,(name,p.stdout,p.stderr)
run('clean copied packet',True)
(F/'data/DERIVATION.md').write_bytes(base+b'\nmutation\n');run('changed payload',False);(F/'data/DERIVATION.md').write_bytes(base)
(F/'data/DERIVATION.md').unlink();run('missing payload',False);(F/'data/DERIVATION.md').write_bytes(base)
(F/'.extra').write_text('extra');run('extra hidden payload',False);(F/'.extra').unlink()
run('wrong detached manifest anchor',False,'0'*64)
run('restored copied packet',True)
(R/'private/controls/results.json').write_text(json.dumps({'scope':'copied two-payload synthetic fixture; no original packet manifest reused; artifact controls only','cases':results,'fixture_detached':{'MANIFEST':m,'REPORT':r,'FINAL':f}},indent=2)+'\n')
print('six copied cases checked; each verifier invocation left its fixture unchanged')
