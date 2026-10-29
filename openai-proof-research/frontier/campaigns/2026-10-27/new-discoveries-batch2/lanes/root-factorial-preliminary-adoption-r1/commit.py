import json,subprocess
from pathlib import Path
root=Path(__file__).resolve().parent; B=root.parents[1]; repo=B.parents[4]
paths=[B/'NEXT.md']; omitted=[]
lanes=[root,root.parent/'root-renyi-component-adoption-r1',root.parent/'sol-factorial-product-preliminary-review-r1',root.parent/'sol-renyi-threshold-source-formal-r1']
for lane in lanes:
    for p in lane.rglob('*'):
        if not p.is_file() or '__pycache__' in p.parts or p.name=='commit-paths.txt':continue
        if p.name.endswith(('.pyc','.olean','.olean.private','.olean.server','.ilean','.ir','.ir.sig','.o','.so')):continue
        if p.stat().st_size>10*1024*1024:
            omitted.append({'path':str(p.relative_to(repo)),'bytes':p.stat().st_size});continue
        paths.append(p)
note=root/'unstaged-bulk-evidence.json';note.write_text(json.dumps(omitted,indent=2)+'\n');paths.append(note)
spec=root/'commit-paths.txt';spec.write_text('\n'.join(sorted(set(str(p.relative_to(repo)) for p in paths)))+'\n')
git=['git','-c','core.packedGitWindowSize=16m','-c','core.packedGitLimit=64m','-c','index.threads=1','-c','core.preloadIndex=false','-c','gc.auto=0']
subprocess.run(git+['add','-f','--pathspec-from-file='+str(spec)],cwd=repo,check=True)
subprocess.run(git+['commit','--quiet','-m','Adopt factorial preliminary review and Renyi partial formal component','--pathspec-from-file='+str(spec)],cwd=repo,check=True)
subprocess.run(git+['log','-1','--format=%h %s'],cwd=repo,check=True)
