"""Run once. All writes constrained to this assigned root. Synthetic controls first."""
from pathlib import Path
import hashlib,json,os,shutil,subprocess,sys
ROOT=Path.cwd()/'frontier/campaigns/2026-10-14/fresh-arithmetic-discovery-r114'
E={'FINAL.md','MANIFEST.json','REPORT.md'}
def sha(b): return hashlib.sha256(b).hexdigest()
def inv(root):
 files={};dirs=[]
 for base,ds,fs in os.walk(root):
  for name in ds: dirs.append(str((Path(base)/name).relative_to(root)))
  for name in fs:
   p=Path(base)/name;b=p.read_bytes();files[str(p.relative_to(root))]={'size':len(b),'sha256':sha(b)}
 return files,sorted(dirs)
def manifest(root,kind):
 files,dirs=inv(root)
 m=dict(schema='r114-exact-v1',kind=kind,envelopes=sorted(E),files={k:v for k,v in files.items() if k not in E},directories=dirs)
 (root/'MANIFEST.json').write_text(json.dumps(m,indent=2,sort_keys=True)+'\n')
 return {name:sha((root/name).read_bytes()) for name in E}
def invoke(root,anchors):
 cmd=[sys.executable,str(root/'packet/verify.py'),str(root)]
 for name,flag in [('FINAL.md','final'),('MANIFEST.json','manifest'),('REPORT.md','report')]:cmd+=['--'+flag,anchors[name]]
 before=inv(root);r=subprocess.run(cmd,cwd=Path.cwd(),capture_output=True,text=True,timeout=20);assert inv(root)==before,'verifier wrote fixture'
 return r
assert not (ROOT/'MANIFEST.json').exists(), 'research seal already exists'
f=ROOT/'controls/fixture';assert not f.exists(),'fixture already exists';(f/'packet').mkdir(parents=True)
shutil.copyfile(ROOT/'packet/tools/verify.py',f/'packet/verify.py')
(f/'packet/a.txt').write_text('synthetic data, not an incoming original archive\n')
(f/'FINAL.md').write_text('SYNTHETIC reduced control only\n');(f/'REPORT.md').write_text('Its own membership; no inherited original certificate\n')
a=manifest(f,'synthetic-control');results=[]
def test(name,anchors,expected):
 r=invoke(f,anchors);assert (r.returncode==0)==expected,(name,r.stdout,r.stderr)
 results.append(dict(case=name,expected_pass=expected,exit_code=r.returncode,output=r.stdout.strip(),read_only=True))
test('baseline',a,True)
b=(f/'packet/a.txt').read_bytes();(f/'packet/a.txt').write_bytes(b+b'changed');test('changed payload',a,False);(f/'packet/a.txt').write_bytes(b)
(f/'packet/a.txt').unlink();test('missing payload',a,False);(f/'packet/a.txt').write_bytes(b)
(f/'.extra').write_text('hidden');test('hidden extra file',a,False);(f/'.extra').unlink()
(f/'empty-extra').mkdir();test('extra empty directory',a,False);(f/'empty-extra').rmdir()
bad=dict(a);bad['MANIFEST.json']='0'*64;test('wrong detached anchor',bad,False)
test('restored baseline',a,True)
(ROOT/'controls/receipt.json').write_text(json.dumps(dict(scope='synthetic reduced fixture; not original archive verification',anchors=a,cases=results),indent=2)+'\n')
anchors=manifest(ROOT,'research')
print(json.dumps(dict(anchors=anchors,control_cases=len(results)),indent=2))
