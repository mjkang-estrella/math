import subprocess,json,hashlib
from pathlib import Path
r=Path(__file__).resolve().parent;B=r.parents[1];repo=B.parents[4]
git=['git','-c','core.packedGitWindowSize=16m','-c','core.packedGitLimit=64m','-c','index.threads=1','-c','core.preloadIndex=false','-c','gc.auto=0'];paths=[];bulk=[]
for d in [r,r.parent/'sol-factorial-product-manuscript-packet-r1']:
 for p in sorted(d.rglob('*')):
  if not p.is_file() or '__pycache__' in p.parts or 'python-deps' in p.relative_to(d).parts or p.name=='commit-paths.txt':continue
  if p.name.endswith(('.pyc','.olean','.olean.private','.olean.server','.ilean','.ir','.ir.sig','.o','.so')):continue
  if p.stat().st_size>10*1024*1024:
   h=hashlib.sha256()
   with p.open('rb') as f:
    while b:=f.read(65536):h.update(b)
   bulk.append({'path':str(p.relative_to(repo)),'bytes':p.stat().st_size,'sha256':h.hexdigest()});continue
  paths.append(str(p.relative_to(repo)))
(r/'unstaged-bulk-evidence.json').write_text(json.dumps(bulk,indent=2)+'\n')
paths.extend([str((B/'NEXT.md').relative_to(repo)),str((r/'unstaged-bulk-evidence.json').relative_to(repo))])
f=r/'commit-paths.txt';f.write_text('\n'.join(sorted(set(paths)))+'\n')
subprocess.run(git+['add','-f','--pathspec-from-file='+str(f)],cwd=repo,check=True)
subprocess.run(git+['commit','--quiet','-m','Freeze factorial manuscript and reproduce portable proof packet','--pathspec-from-file='+str(f)],cwd=repo,check=True)
print(subprocess.check_output(git+['log','-1','--format=%h %s'],cwd=repo,text=True).strip())
