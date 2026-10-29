from pathlib import Path
import hashlib,json,subprocess
P=Path(__file__).resolve().parent;B=P.parents[1];repo=B.parents[4];S=P.parent/'sol-fresh-source-discovery-r136'
def sha(p):
 h=hashlib.sha256()
 with p.open('rb') as f:
  for c in iter(lambda:f.read(1048576),b''):h.update(c)
 return h.hexdigest()
for r in json.loads((P/'review-freeze.json').read_text())['files']:assert sha(S/r['path'])==r['sha256']
assert sha(P/'exact-replay/certificate.json')==sha(S/'certificate.json')
(P/'replay-receipt.json').write_text(json.dumps({'status':'PASS','byte_identical_certificate':True,'candidate_hashes_unchanged':59,'qualification':'Copied implementation replay, not independent checker; ordinary proof separately rederived.','credit':0,'additional':9,'total':39},indent=2)+'\n')
intro='''r136 Frank-copula attenuation has a complete ordinary refutation candidate.
Root rederived the smooth regression/Rayleigh/monotone-quantization bridge,
verified 57 manifest and 21 scientific-freeze entries, and reproduced the exact
20-category rational separation certificate byte-identically. Substantive
eligibility remains HOLD: a classical maximal-correlation adaptation may
subsume it. Independent Sol review is launched before Lean or paper investment.
See root-frank-attenuation-preliminary-freeze-r1. Credit0; counts9/39.

'''
n=(B/'NEXT.md').read_text();assert 'r136 Frank-copula attenuation has' not in n
(B/'NEXT.md').write_text(n.replace('# Current continuation — 29 October 2026\n','# Current continuation — 29 October 2026\n\n'+intro,1))
paths=[B/'NEXT.md'];bulk=[]
for base in [P,S]:
 for p in sorted(base.rglob('*')):
  if not p.is_file() or '__pycache__' in p.parts or p.name=='commit-paths.txt' or p.suffix in {'.pyc','.olean','.ilean','.ir','.o','.so'}:continue
  if p.stat().st_size>10485760:bulk.append({'path':str(p.relative_to(repo)),'bytes':p.stat().st_size,'sha256':sha(p)})
  else:paths.append(p)
bp=P/'unstaged-bulk-evidence.json';bp.write_text(json.dumps(bulk,indent=2)+'\n');paths.append(bp)
ps=P/'commit-paths.txt';ps.write_text(''.join(str(p.relative_to(repo))+'\n' for p in sorted(set(paths))))
git=['git','-c','core.packedGitWindowSize=16m','-c','core.packedGitLimit=64m','-c','index.threads=1','-c','core.preloadIndex=false','-c','gc.auto=0']
subprocess.run(git+['add','-f','--pathspec-from-file='+str(ps)],cwd=repo,check=True)
subprocess.run(git+['commit','-m','Freeze Frank attenuation refutation for substantive review','--pathspec-from-file='+str(ps)],cwd=repo,check=True,stdout=subprocess.DEVNULL)
subprocess.run(git+['log','-1','--format=%h %s'],cwd=repo,check=True)
