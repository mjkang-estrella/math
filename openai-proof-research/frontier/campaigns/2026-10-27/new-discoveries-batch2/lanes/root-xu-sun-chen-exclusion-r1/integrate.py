from pathlib import Path
import hashlib,json,subprocess
P=Path(__file__).resolve().parent;B=P.parents[1];repo=B.parents[4];S=P.parent/"sol-xu-sun-chen-preliminary-review-r1"
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
intro="Xu–Sun–Chen Conjectures 2/3: source and ordinary mathematics PASS, but root\nadopts routine-source-method EXCLUDE. The source cubic-to-candidate quartic\nsign change is fully checked, not assumed. All 215 positive coefficients\nreproduce independently; minimum 584325 (constant 786520). All 28 candidate\nand 45 review payload paths match. Novelty HOLD remains; no Lean investment.\nSee root-xu-sun-chen-exclusion-r1. Sol r164 replaces the review.\nCounts unchanged: 9/39, next40.\n\n"
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
subprocess.run(git+['commit','-m',"Exclude Shafer-Fink proofs as routine source-method adaptations",'--pathspec-from-file='+str(ps)],cwd=repo,check=True,stdout=subprocess.DEVNULL)
subprocess.run(git+['log','-1','--format=%h %s'],cwd=repo,check=True)
