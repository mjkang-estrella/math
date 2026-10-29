from pathlib import Path
import subprocess,json
root=Path(__file__).resolve().parent;B=root.parents[1];repo=B.parents[4]
p=B/'NEXT.md';text=p.read_text().replace('fresh discovery r114; two freed slots reserved for fresh discovery r115 and focused Renyi current/historical prior review.','fresh discovery r114 and r115 plus focused Renyi current/historical prior review (all launched; receipts in root-renyi-preliminary-adoption-r1/launch-receipts.json).',1);p.write_text(text)
paths=[p];omitted=[]
names=['root-fresh-source-r112-r113-handbacks','sol-fresh-source-discovery-r112','sol-fresh-source-discovery-r113','root-renyi-preliminary-adoption-r1','sol-renyi-threshold-preliminary-review-r1']
for name in names:
    for f in (root.parent/name).rglob('*'):
        if not f.is_file() or '__pycache__' in f.parts or f.suffix in ['.pyc','.olean','.ilean'] or f.name=='commit-paths.txt':continue
        if f.stat().st_size>10*1024*1024:omitted.append({'path':str(f.relative_to(repo)),'bytes':f.stat().st_size,'status':'Bulk survey cache retained on disk and worker-manifest bound; not staged'})
        else:paths.append(f)
record=root/'unstaged-bulk-evidence.json';record.write_text(json.dumps(omitted,indent=2)+'\n');paths.append(record)
spec=root/'commit-paths.txt';spec.write_text(''.join(str(f.relative_to(repo))+'\n' for f in sorted(set(paths))))
git=['git','-c','core.packedGitWindowSize=16m','-c','core.packedGitLimit=64m','-c','index.threads=1','-c','core.preloadIndex=false','-c','gc.auto=0']
subprocess.run(git+['add','-f','--pathspec-from-file='+str(spec)],cwd=repo,check=True)
subprocess.run(git+['commit','--quiet','-m','Adopt scoped Renyi review and record matroid and ring research dispositions','--pathspec-from-file='+str(spec)],cwd=repo,check=True)
subprocess.run(git+['log','-1','--format=%h %s'],cwd=repo,check=True)
