import subprocess, sys
from pathlib import Path
root=Path(__file__).resolve().parent
B=root.parents[1]
repo=B.parents[4]
n=int(sys.argv[1]); assert n in (85,87)
paths=[]
for folder in (B/'lanes'/f'sol-fresh-source-discovery-r{n}', B/'lanes'/f'root-fresh-source-r{n}-handback'):
    for p in folder.rglob('*'):
        if p.is_file() and '__pycache__' not in p.parts and '.git' not in p.parts and p.suffix not in ('.pyc','.olean','.ilean') and p.name!='commit-paths.txt':
            paths.append(str(p.relative_to(repo)))
if n==87: paths.append(str((B/'NEXT.md').relative_to(repo)))
spec=B/'lanes'/f'root-fresh-source-r{n}-handback'/'commit-paths.txt'
spec.write_text('\n'.join(sorted(paths))+'\n')
git=['git','-c','core.packedGitWindowSize=16m','-c','core.packedGitLimit=64m','-c','index.threads=1','-c','core.preloadIndex=false','-c','gc.auto=0']
subprocess.run(git+['add','-f','--pathspec-from-file='+str(spec)],cwd=repo,check=True)
subprocess.run(git+['commit','--quiet','-m',f'Preserve unresolved r{n} research and root diagnostic checks','--pathspec-from-file='+str(spec)],cwd=repo,check=True)
subprocess.run(git+['log','-1','--format=%h %s'],cwd=repo,check=True)
