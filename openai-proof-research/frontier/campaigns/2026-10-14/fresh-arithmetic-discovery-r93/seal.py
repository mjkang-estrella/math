from pathlib import Path
import json,hashlib,stat
r=Path(__file__).resolve().parent;p=r/'packet'
def sha(q):return hashlib.sha256(q.read_bytes()).hexdigest()
files={};dirs={'.':stat.S_IMODE(p.stat().st_mode)}
for q in sorted(p.rglob('*')):
 assert not q.is_symlink()
 s=q.stat();rel=q.relative_to(p).as_posix()
 if q.is_dir():dirs[rel]=stat.S_IMODE(s.st_mode)
 elif rel!='MANIFEST.json':
  assert s.st_nlink==1
  files[rel]={'sha256':sha(q),'bytes':s.st_size,'mode':stat.S_IMODE(s.st_mode),'nlink':s.st_nlink}
m={'schema':'exact-packet-v1','files':files,'directories':sorted(dirs),'directory_modes':dirs}
mp=p/'MANIFEST.json';mp.write_text(json.dumps(m,indent=2,sort_keys=True)+'\n')
rootfiles={q.name:{'sha256':sha(q),'bytes':q.stat().st_size} for q in sorted(r.iterdir()) if q.is_file() and q.name not in {'FINAL.json','CONTROLS.json','VERIFICATION.json','HANDOFF.md'}}
f={'schema':'arithmetic-r93-v1','pin':'fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb','status':'AUTHOR_PROOF_FOR_INDEPENDENT_ASSESSMENT','gates':{'correctness':None,'contribution':None,'acceptance':None},'manifest_sha256':sha(mp),'report_sha256':sha(r/'REPORT.md'),'frozen_sha256':sha(p/'public/FROZEN.md'),'tree_sha256':'eeecc1da49aa02877d137c4fb90339aca460ec27718b623916368bc08dc5e09b','root_files':rootfiles}
(r/'FINAL.json').write_text(json.dumps(f,indent=2,sort_keys=True)+'\n')
print(json.dumps({'FINAL':sha(r/'FINAL.json'),'REPORT':sha(r/'REPORT.md'),'MANIFEST':sha(mp),'files':len(files),'dirs':len(dirs)},indent=2))
