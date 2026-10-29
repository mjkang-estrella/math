from pathlib import Path
import subprocess,json
root=Path(__file__).resolve().parent;B=root.parents[1];repo=B.parents[4]
paths=[B/'NEXT.md'];omitted=[]
for lane in [root,root.parent/'sol-fresh-source-discovery-r111']:
    for f in lane.rglob('*'):
        if not f.is_file() or '__pycache__' in f.parts or f.suffix in ['.pyc','.olean','.ilean'] or f.name=='commit-paths.txt':continue
        if f.stat().st_size>10*1024*1024:
            omitted.append({'path':str(f.relative_to(repo)),'bytes':f.stat().st_size,'reason':'Bulk duplicate-screen corpus/cache retained on disk, hash-bound by manifest/freeze; not staged into git.'})
        else:paths.append(f)
record=root/'unstaged-bulk-evidence.json';record.write_text(json.dumps(omitted,indent=2)+'\n');paths.append(record)
spec=root/'commit-paths.txt';spec.write_text(''.join(str(f.relative_to(repo))+'\n' for f in sorted(set(paths))))
git=['git','-c','core.packedGitWindowSize=16m','-c','core.packedGitLimit=64m','-c','index.threads=1','-c','core.preloadIndex=false','-c','gc.auto=0']
subprocess.run(git+['add','-f','--pathspec-from-file='+str(spec)],cwd=repo,check=True)
subprocess.run(git+['commit','--quiet','-m','Freeze full Renyi threshold refutation candidate for independent review','--pathspec-from-file='+str(spec)],cwd=repo,check=True)
subprocess.run(git+['log','-1','--format=%h %s'],cwd=repo,check=True)
