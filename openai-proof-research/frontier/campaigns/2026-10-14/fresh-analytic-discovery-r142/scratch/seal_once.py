from pathlib import Path
import hashlib,json,os,subprocess,sys
R=Path.cwd();manifest=R/'MANIFEST.json';assert not manifest.exists(),'seal already exists'
E={'FINAL.md','MANIFEST.json','REPORT.md'}
def sha(b):return hashlib.sha256(b).hexdigest()
def snapshot():
 files={};dirs=[]
 for base,ds,fs in os.walk(R,followlinks=False):
  for n in ds:
   p=Path(base)/n;assert not p.is_symlink();dirs.append(str(p.relative_to(R)))
  for n in fs:
   p=Path(base)/n;assert p.is_file() and not p.is_symlink() and p.stat().st_nlink==1
   b=p.read_bytes();files[str(p.relative_to(R))]={'size':len(b),'sha256':sha(b)}
 return files,sorted(dirs)
files,dirs=snapshot()
m={'schema':'r142-exact-payload-v1','outside_envelopes':sorted(E),'directories':dirs,'files':[{'path':p,**r} for p,r in sorted(files.items()) if p not in E]}
manifest.write_text(json.dumps(m,indent=2)+'\n')
# External executable provides detached anchors, independently recomputed below.
r=subprocess.run(['sha256sum','FINAL.md','MANIFEST.json','REPORT.md'],check=True,capture_output=True,text=True)
anchors={line.split()[1]:line.split()[0] for line in r.stdout.splitlines()}
for p,h in anchors.items():assert sha((R/p).read_bytes())==h
before=snapshot()
cmd=[sys.executable,'verify.py',str(R),'--project','/home/mj-kang/Documents/Dev/math/openai-proof-research','--final-sha',anchors['FINAL.md'],'--manifest-sha',anchors['MANIFEST.json'],'--report-sha',anchors['REPORT.md']]
v=subprocess.run(cmd,capture_output=True,text=True,timeout=40)
assert before==snapshot(),'post-seal verification wrote files'
print(v.stdout,end='');print(v.stderr,end='');assert v.returncode==0
print(r.stdout,end='');print('ONE MAIN SEAL; WHOLE-ROOT SNAPSHOT UNCHANGED BY VERIFICATION; ARTIFACTS ONLY')
