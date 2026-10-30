from pathlib import Path
import hashlib,json,subprocess
P=Path(__file__).resolve().parent;B=P.parents[1];repo=B.parents[4];S=P.parent/"sol-sirola-dumas-preliminary-review-r1"
def sha(p):
 with p.open('rb') as f:return hashlib.file_digest(f,'sha256').hexdigest()
for r in json.loads((S/"finalhashes.json").read_text())['files']:
 p=S/r['path'];assert sha(p)==r['sha256'] and p.stat().st_size==r['bytes']
if S.name.startswith('sol-sirola'):
 for r in json.loads((P.parent/'root-r163-preliminary-freeze-r1/review-freeze.json').read_text())['files']:
  p=Path(r['path']);assert sha(p)==r['sha256'] and p.stat().st_size==r['bytes']
assert json.loads((P/'replay-receipt.json').read_text())['status']=='PASS'
l=json.loads((B/'ledger.json').read_text());assert l['accepted_count']==9 and l['total_accepted_count']==39
intro="Sirola Dumas conjecture: full ordinary proof and complete El Fadil2023\nbridge independently PASS; root adopts routine classical EXCLUDE. Arbitrary\ndomains require only persistence of factors into Frac(R), not converse Gauss.\nFirst-kind reciprocal and value-group normalization close all hypotheses.\nRoot independent replay18506 initial-form products/1592 normalization cases;\n50 originals/63 review payload paths unchanged. No Lean/paper investment.\nSee root-sirola-dumas-exclusion-r1. Sol r167 replaces review; r165/r166 continue.\nCounts unchanged9 additional/39 total,next40.\n\n"
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
subprocess.run(git+['commit','-m',"Exclude Dumas conjecture proof by complete classical bridge",'--pathspec-from-file='+str(ps)],cwd=repo,check=True,stdout=subprocess.DEVNULL)
subprocess.run(git+['log','-1','--format=%h %s'],cwd=repo,check=True)
