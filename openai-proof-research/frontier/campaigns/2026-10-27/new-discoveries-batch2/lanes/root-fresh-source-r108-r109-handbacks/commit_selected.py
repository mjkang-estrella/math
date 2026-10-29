from pathlib import Path
import subprocess
root=Path(__file__).resolve().parent
B=root.parents[1]
repo=B.parents[4]
paths=[B/'NEXT.md']
for lane in [root,root.parent/'sol-fresh-source-discovery-r108',root.parent/'sol-fresh-source-discovery-r109']:
    paths += [p for p in lane.rglob('*') if p.is_file() and '__pycache__' not in p.parts and p.suffix not in ['.pyc','.olean','.ilean'] and p.name!='commit-paths.txt']
spec=root/'commit-paths.txt'
spec.write_text(''.join(str(p.relative_to(repo))+'\n' for p in sorted(set(paths))))
git=['git','-c','core.packedGitWindowSize=16m','-c','core.packedGitLimit=64m','-c','index.threads=1','-c','core.preloadIndex=false','-c','gc.auto=0']
subprocess.run(git+['add','-f','--pathspec-from-file='+str(spec)],cwd=repo,check=True)
subprocess.run(git+['commit','--quiet','-m','Record packing construction review hold and unresolved join bound','--pathspec-from-file='+str(spec)],cwd=repo,check=True)
subprocess.run(git+['log','-1','--format=%h %s'],cwd=repo,check=True)
