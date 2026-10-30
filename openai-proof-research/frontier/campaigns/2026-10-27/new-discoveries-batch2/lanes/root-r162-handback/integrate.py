from pathlib import Path
import hashlib,json,subprocess
P=Path(__file__).resolve().parent;B=P.parents[1];repo=B.parents[4];S=P.parent/"sol-fresh-source-discovery-r162"
def sha(p):
 with p.open('rb') as f:return hashlib.file_digest(f,'sha256').hexdigest()
assert json.loads((P/'replay-receipt.json').read_text())['status']=='PASS'
ledger=json.loads((B/'ledger.json').read_text());assert ledger['accepted_count']==9 and ledger['total_accepted_count']==39
json.loads((B/'prior-campaign-context.json').read_text())
if (S/'final-hashes.json').exists():
 rows=json.loads((S/'final-hashes.json').read_text())['files']
 for r in rows:
  p=S/r['path'];assert sha(p)==r['sha256'] and p.stat().st_size==r['bytes']
 for r in json.loads((P.parent/'root-r160-preliminary-freeze-r1/review-freeze.json').read_text())['files']:
  p=Path(r['path']);assert sha(p)==r['sha256'] and p.stat().st_size==r['bytes']
else:
 for path,r in json.loads((S/'finalmanifest.json').read_text())['entries'].items():
  p=S/path;assert sha(p)==r['sha256'] and p.stat().st_size==r['bytes']
 for r in json.loads((P/'replay/triangle-checks.json').read_text()):assert r['s']<=r['bound']
intro="r162 Achour saturation Conjecture1 remains unresolved: independent exposed\nset with a sufficiently large size and perfectly matchable complement is\nmissing. Root replays 771 small graphs, 48 cubic samples and 31 triangle\nsystems; no universal result. Planar graphical Stirling unimodality is\nexcluded by an actual earlier public counterexample. All 54 payload / 50\nscientific paths match; failures and coverage gaps retained.\nSee root-r162-handback. Sol r165 replaces r162; r163 and r164 continue.\nCounts unchanged: 9/39, next40.\n\n"
n=(B/'NEXT.md').read_text();heading='# Current continuation — 29 October 2026\n'
assert intro not in n and heading in n
(B/'NEXT.md').write_text(n.replace(heading,heading+'\n'+intro,1))
paths=[B/'NEXT.md'];bulk=[]
for base in [P,S]:
 for p in sorted(base.rglob('*')):
  if not p.is_file() or '__pycache__' in p.parts or p.name=='commit-paths.txt' or any(p.name.endswith(x) for x in ['.pyc','.olean','.olean.private','.olean.server','.ilean','.ir','.ir.sig','.o','.so']):continue
  if p.stat().st_size>10485760:bulk.append({'path':str(p.relative_to(repo)),'bytes':p.stat().st_size,'sha256':sha(p)})
  else:paths.append(p)
bp=P/'unstaged-bulk-evidence.json';bp.write_text(json.dumps(bulk,indent=2)+'\n');paths.append(bp)
ps=P/'commit-paths.txt';ps.write_text(''.join(str(p.relative_to(repo))+'\n' for p in sorted(set(paths))))
git=['git','-c','core.packedGitWindowSize=16m','-c','core.packedGitLimit=64m','-c','index.threads=1','-c','core.preloadIndex=false','-c','gc.auto=0']
subprocess.run(git+['add','-f','--pathspec-from-file='+str(ps)],cwd=repo,check=True)
subprocess.run(git+['commit','-m',"Record saturation proof gap and prior Stirling counterexample",'--pathspec-from-file='+str(ps)],cwd=repo,check=True,stdout=subprocess.DEVNULL)
subprocess.run(git+['log','-1','--format=%h %s'],cwd=repo,check=True)
