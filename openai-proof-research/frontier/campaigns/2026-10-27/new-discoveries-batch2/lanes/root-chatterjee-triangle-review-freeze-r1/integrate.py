from pathlib import Path
import subprocess
root=Path(__file__).resolve().parent;B=root.parents[1];repo=B.parents[4];lane=root.parent/'sol-fresh-source-discovery-r97'
p=B/'NEXT.md';txt=p.read_text().replace('fresh analytic/geometric r97.','independent Chatterjee triangle review r1. r97 supplies a full ordinary all-K multiplicative triangle refutation for directed/average/max Chatterjee distances, with joint density and positive pair distances. Root checked78 exact directed values/26ratios, verified58manifestentries and froze59files. Routine modulo/shuffle adaptation, final-source comparison and informal approximate-scope attribution remain review gates. No Lean/paper/credit. See root-chatterjee-triangle-review-freeze-r1/ADOPTION.json.');p.write_text(txt)
paths=[p]
for folder in (root,lane):paths.extend(q for q in folder.rglob('*') if q.is_file() and '__pycache__' not in q.parts and q.name!='commit-paths.txt' and q.suffix not in ('.pyc','.olean','.ilean'))
spec=root/'commit-paths.txt';spec.write_text('\n'.join(str(q.relative_to(repo)) for q in sorted(set(paths)))+'\n')
git=['git','-c','core.packedGitWindowSize=16m','-c','core.packedGitLimit=64m','-c','index.threads=1','-c','core.preloadIndex=false','-c','gc.auto=0']
subprocess.run(git+['add','-f','--pathspec-from-file='+str(spec)],cwd=repo,check=True)
subprocess.run(git+['commit','--quiet','-m','Freeze full Chatterjee triangle refutation for independent review','--pathspec-from-file='+str(spec)],cwd=repo,check=True)
subprocess.run(git+['log','-1','--format=%h %s'],cwd=repo,check=True)
