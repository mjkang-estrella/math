from pathlib import Path
import hashlib,json,subprocess
P=Path(__file__).resolve().parent;B=P.parents[1];repo=B.parents[4]
paths=[B/'NEXT.md'];bulk=[]
for base in [P,P.parent/'sol-fresh-source-discovery-r120']:
 for p in sorted(base.rglob('*')):
  if not p.is_file() or '__pycache__' in p.parts or p.name=='commit-paths.txt' or p.suffix in {'.pyc','.olean','.ilean','.ir','.o','.so'}:continue
  if p.stat().st_size>10485760:
   h=hashlib.sha256()
   with p.open('rb') as f:
    for c in iter(lambda:f.read(1048576),b''):h.update(c)
   bulk.append({'path':str(p.relative_to(repo)),'bytes':p.stat().st_size,'sha256':h.hexdigest()})
  else:paths.append(p)
out=P/'unstaged-bulk-evidence.json';out.write_text(json.dumps(bulk,indent=2)+'\n');paths.append(out)
ps=P/'commit-paths.txt';ps.write_text(''.join(str(p.relative_to(repo))+'\n' for p in sorted(set(paths))))
git=['git','-c','core.packedGitWindowSize=16m','-c','core.packedGitLimit=64m','-c','index.threads=1','-c','core.preloadIndex=false','-c','gc.auto=0']
subprocess.run(git+['add','-f','--pathspec-from-file='+str(ps)],cwd=repo,check=True)
subprocess.run(git+['commit','-m','Record r120 Nielsen public and routine exclusions','--pathspec-from-file='+str(ps)],cwd=repo,check=True,stdout=subprocess.DEVNULL)
subprocess.run(git+['log','-1','--format=%h %s'],cwd=repo,check=True)
