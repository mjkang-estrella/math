from pathlib import Path
import subprocess
root=Path(__file__).resolve().parent;B=root.parents[1];repo=B.parents[4]
p=B/'NEXT.md';s=p.read_text().replace('freed prior-review slot reserved for exact Renyi registry-gap closure.','exact Renyi registry-gap closure launched (receipt in root-renyi-prior-adoption-r2/launch-receipt.json).',1);p.write_text(s)
paths=[p]
for lane in [root,root.parent/'sol-renyi-threshold-current-prior-review-r2']:
    paths += [f for f in lane.rglob('*') if f.is_file() and '__pycache__' not in f.parts and f.suffix not in ['.pyc','.olean','.ilean'] and f.name!='commit-paths.txt']
spec=root/'commit-paths.txt';spec.write_text(''.join(str(f.relative_to(repo))+'\n' for f in sorted(set(paths))))
git=['git','-c','core.packedGitWindowSize=16m','-c','core.packedGitLimit=64m','-c','index.threads=1','-c','core.preloadIndex=false','-c','gc.auto=0']
subprocess.run(git+['add','-f','--pathspec-from-file='+str(spec)],cwd=repo,check=True)
subprocess.run(git+['commit','--quiet','-m','Record Renyi prior-body comparison and exact registry coverage gaps','--pathspec-from-file='+str(spec)],cwd=repo,check=True)
subprocess.run(git+['log','-1','--format=%h %s'],cwd=repo,check=True)
