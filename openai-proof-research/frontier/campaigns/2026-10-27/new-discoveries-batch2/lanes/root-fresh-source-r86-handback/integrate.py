import subprocess
from pathlib import Path
root=Path(__file__).resolve().parent;B=root.parents[1];repo=B.parents[4]
paths=[]
for folder in (root,root.parent/'sol-fresh-source-discovery-r86'):
    paths += [str(p.relative_to(repo)) for p in folder.rglob('*') if p.is_file() and '__pycache__' not in p.parts and p.name!='commit-paths.txt' and p.suffix not in ('.pyc','.olean','.ilean')]
paths += [str((B/name).relative_to(repo)) for name in ('NEXT.md','ledger.json')]
spec=root/'commit-paths.txt';spec.write_text('\n'.join(sorted(paths))+'\n')
git=['git','-c','core.packedGitWindowSize=16m','-c','core.packedGitLimit=64m','-c','index.threads=1','-c','core.preloadIndex=false','-c','gc.auto=0']
subprocess.run(git+['add','-f','--pathspec-from-file='+str(spec)],cwd=repo,check=True)
subprocess.run(git+['commit','--quiet','-m','Exclude routine retail unimodality reduction and preserve source holds','--pathspec-from-file='+str(spec)],cwd=repo,check=True)
subprocess.run(git+['log','-1','--format=%h %s'],cwd=repo,check=True)
