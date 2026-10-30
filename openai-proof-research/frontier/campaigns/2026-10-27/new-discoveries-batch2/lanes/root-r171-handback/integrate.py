from pathlib import Path
import hashlib,json,subprocess,sys
P=Path(sys.argv[1]).resolve() if len(sys.argv)>1 else Path(__file__).resolve().parent
B=P.parents[1];repo=B.parents[4]
is_cycle=P.name=='root-r171-handback'
S=P.parent/('sol-fresh-source-discovery-r171' if is_cycle else 'sol-pendulum-manuscript-packet-r1')
def sha(p):
 with p.open('rb') as f:return hashlib.file_digest(f,'sha256').hexdigest()
for r in json.loads((P/'review-freeze.json').read_text())['files']:
 p=Path(r['path']);assert p.stat().st_size==r['bytes'] and sha(p)==r['sha256'],str(p)
assert json.loads((P/'verification-receipt.json').read_text())['status']=='PASS'
l=json.loads((B/'ledger.json').read_text());assert l['accepted_count']==9 and l['total_accepted_count']==39
intro=('Cycle congruence r171 remains unresolved: universal cyclic rank identity missing. Root private replay is byte-identical; 58 scientific/59 manifest entries and61 original files verify. Finite modular ranks are not characteristic-zero all-order proof. Zero credit; fresh finite/algebraic r172 assigned. See root-r171-handback. Counts9additional/39total,next40.' if is_cycle else 'Pendulum final merged source archive: ROOT fresh extracted replay PASS,14 mathematical modules/139 actual audited declarations; rebuilt ZIP byte-identical. Full literal source_claim closed. Manuscript text delivered; authored PDF and visual QA NOT completed because required Node marker fails under fixed memory guard. Independent source/math/formal/manuscript-source review assigned; production and historical-priority holds remain. See root-pendulum-merged-packet-adoption-r1. Fresh r170/r172 research continues. No acceptance/count change:9additional/39total,next40.')+'\n\n'
n=(B/'NEXT.md').read_text();heading='# Current continuation — 29 October 2026\n';assert heading in n and intro not in n
(B/'NEXT.md').write_text(n.replace(heading,heading+'\n'+intro,1))
paths=[B/'NEXT.md'];bulk=[]
for base in [P,S]:
 for p in sorted(base.rglob('*')):
  if not p.is_file() or '__pycache__' in p.parts or p.name=='commit-paths.txt' or any(p.name.endswith(x) for x in ['.pyc','.olean','.olean.private','.olean.server','.ilean','.ir','.ir.sig','.o','.so']):continue
  if p.stat().st_size>10485760:bulk.append(dict(path=str(p.relative_to(repo)),bytes=p.stat().st_size,sha256=sha(p)))
  else:paths.append(p)
bp=P/'unstaged-bulk-evidence.json';bp.write_text(json.dumps(bulk,indent=2)+'\n');paths.append(bp)
ps=P/'commit-paths.txt';ps.write_text(''.join(str(p.relative_to(repo))+'\n' for p in sorted(set(paths))))
git=['git','-c','core.packedGitWindowSize=16m','-c','core.packedGitLimit=64m','-c','index.threads=1','-c','core.preloadIndex=false','-c','gc.auto=0']
subprocess.run(git+['add','-f','--pathspec-from-file='+str(ps)],cwd=repo,check=True)
message='Record unresolved cycle rank handback and refill research slot' if is_cycle else 'Verify merged pendulum theorem packet and commission independent review'
subprocess.run(git+['commit','-m',message,'--pathspec-from-file='+str(ps)],cwd=repo,check=True,stdout=subprocess.DEVNULL)
subprocess.run(git+['log','-1','--format=%h %s'],cwd=repo,check=True)
