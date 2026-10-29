import subprocess,json,hashlib
from pathlib import Path
r=Path(__file__).resolve().parent
lanes=r.parent
B=r.parents[1]
repo=B.parents[4]
git=['git','-c','core.packedGitWindowSize=16m','-c','core.packedGitLimit=64m','-c','index.threads=1','-c','core.preloadIndex=false','-c','gc.auto=0']
groups=[(['sol-fresh-source-discovery-r116'],'Record unresolved Matkowski source investigation'),(['sol-factorial-product-prior-clearance-r2'],'Record bounded factorial product prior clearance'),(['sol-renyi-deficit-source-formal-r2',r.name],'Adopt closed Renyi source endpoint and advance three research lanes')]
bulk=[]
for i,(dirs,msg) in enumerate(groups):
 paths=[]
 for d in dirs:
  for p in sorted((lanes/d).rglob('*')):
   if not p.is_file() or '__pycache__' in p.parts or p.name.startswith('commit-paths') or p.name=='commit-results.json':continue
   if p.name.endswith(('.pyc','.olean','.olean.private','.olean.server','.ilean','.ir','.ir.sig','.o','.so')):continue
   if p.stat().st_size>10*1024*1024:
    h=hashlib.sha256()
    with p.open('rb') as f:
     while b:=f.read(65536):h.update(b)
    bulk.append({'path':str(p.relative_to(repo)),'bytes':p.stat().st_size,'sha256':h.hexdigest()});continue
   paths.append(str(p.relative_to(repo)))
 if i==2:
  (r/'unstaged-bulk-evidence.json').write_text(json.dumps(bulk,indent=2)+'\n')
  paths.extend([str((B/'NEXT.md').relative_to(repo)),str((r/'unstaged-bulk-evidence.json').relative_to(repo))])
 f=r/f'commit-paths-{i}.txt';f.write_text('\n'.join(sorted(set(paths)))+'\n')
 subprocess.run(git+['add','-f','--pathspec-from-file='+str(f)],cwd=repo,check=True)
 subprocess.run(git+['commit','--quiet','-m',msg,'--pathspec-from-file='+str(f)],cwd=repo,check=True)
 q=subprocess.check_output(git+['log','-1','--format=%h %s'],cwd=repo,text=True).strip()
 print(q,flush=True)
