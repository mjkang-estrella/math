from pathlib import Path
import hashlib,json,subprocess
P=Path(__file__).resolve().parent;B=P.parents[1];repo=B.parents[4];T=P.parent/'root-r152-preliminary-freeze-r1'
def sha(p):
 with p.open('rb') as f:return hashlib.file_digest(f,'sha256').hexdigest()
bases=[P,T]
for k,R in [(151,P),(152,T)]:
 S=P.parent/f'sol-fresh-source-discovery-r{k}';bases.append(S)
 for name in ['finalmanifest.json','scientific-freeze.json']:
  for r in json.loads((S/name).read_text())['entries']:assert sha(S/r['path'])==r['sha256'],r['path']
 assert json.loads((R/'replay-receipt.json').read_text())['status']=='PASS'
for r in json.loads((T/'review-freeze.json').read_text())['files']:assert sha(Path(r['path']))==r['sha256']
intro='''r151 geometric smooth-form lifting remains unresolved; Viakhirev is
excluded by an earlier actual public proof. Root verifies 64 manifest/45
scientific entries and replays 432 monomial controls and source checks.
r152 supplies a complete ordinary Kazemi hypercube-coloring proof but proposes
routine-source exclusion. Root freezes34 files, verifies29 manifest/27 science
entries and reproduces controls; independent source/math/eligibility review
is pending, not presumed excluded or accepted. See root-r151-handback and
root-r152-preliminary-freeze-r1. Sol r154 research and Kazemi review replace
the two completed slots; r153 continues. Counts remain 9 additional / 39 total.

'''
n=(B/'NEXT.md').read_text();assert 'r151 geometric smooth-form lifting remains unresolved;' not in n
heading='# Current continuation — 29 October 2026\n';assert heading in n
(B/'NEXT.md').write_text(n.replace(heading,heading+'\n'+intro,1))
paths=[B/'NEXT.md'];bulk=[]
for base in bases:
 for p in sorted(base.rglob('*')):
  if not p.is_file() or '__pycache__' in p.parts or p.name=='commit-paths.txt' or any(p.name.endswith(x) for x in ['.pyc','.olean','.olean.private','.olean.server','.ilean','.ir','.ir.sig','.o','.so']):continue
  if p.stat().st_size>10485760:bulk.append({'path':str(p.relative_to(repo)),'bytes':p.stat().st_size,'sha256':sha(p)})
  else:paths.append(p)
bp=P/'unstaged-bulk-evidence.json';bp.write_text(json.dumps(bulk,indent=2)+'\n');paths.append(bp)
ps=P/'commit-paths.txt';ps.write_text(''.join(str(p.relative_to(repo))+'\n' for p in sorted(set(paths))))
git=['git','-c','core.packedGitWindowSize=16m','-c','core.packedGitLimit=64m','-c','index.threads=1','-c','core.preloadIndex=false','-c','gc.auto=0']
subprocess.run(git+['add','-f','--pathspec-from-file='+str(ps)],cwd=repo,check=True)
subprocess.run(git+['commit','-m','Record geometric lifting gap and freeze Kazemi proof for review','--pathspec-from-file='+str(ps)],cwd=repo,check=True,stdout=subprocess.DEVNULL)
subprocess.run(git+['log','-1','--format=%h %s'],cwd=repo,check=True)
