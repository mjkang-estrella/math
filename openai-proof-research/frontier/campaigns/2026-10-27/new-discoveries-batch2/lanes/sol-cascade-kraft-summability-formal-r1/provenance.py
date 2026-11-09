import os,resource,hashlib,json,re,time
from pathlib import Path
resource.setrlimit(resource.RLIMIT_AS,(512*1024**2,512*1024**2));resource.setrlimit(resource.RLIMIT_CPU,(30,30))
for k in ['OPENBLAS_NUM_THREADS','OMP_NUM_THREADS','MKL_NUM_THREADS','NUMEXPR_NUM_THREADS']:os.environ[k]='1'
b=Path(__file__).resolve().parent; root=Path('/home/mj-kang/Documents/Dev/math');start=time.monotonic()
def sha(p):
 h=hashlib.sha256()
 with p.open('rb') as f:
  for c in iter(lambda:f.read(1024**2),b''):h.update(c)
 return h.hexdigest()
old=json.loads((b/'frozen-before.json').read_text());after={p:sha(Path(p)) for p in old};assert old==after
(b/'frozen-after.json').write_text(json.dumps(after,indent=2)+'\n')
for p,h in old.items():assert sha(b/'formal'/Path(p).name)==h
pkgs=root/'openai-proof-research/frontier/campaigns/2026-10-14/formal/.lake/packages'
leanroot=root/'dlp-research/.tools/lean-4.34.1-linux'
search=[b/'replay/formal']+[p/'.lake/build/lib/lean' for p in sorted(pkgs.iterdir()) if (p/'.lake/build/lib/lean').is_dir()]+[leanroot/'lib/lean']
deps={};missing=[]
for name in (b/'replay/formal/dependencies.txt').read_text().splitlines():
 rel=Path(*name.split('.')).with_suffix('.olean')
 found=next((p/rel for p in search if (p/rel).is_file()),None)
 if found is None:missing.append(name);continue
 deps[str(found)]=sha(found)
 for suffix in ['.private','.server']:
  extra=Path(str(found)+suffix)
  if extra.is_file():deps[str(extra)]=sha(extra)
 # Source hashes where packages expose them; Lean core uses src/lean.
 for sp in [leanroot/'src/lean'/rel.with_suffix('.lean')]+[p/rel.with_suffix('.lean') for p in sorted(pkgs.iterdir())]:
  if sp.is_file():deps[str(sp)]=sha(sp);break
assert not missing,missing
(b/'dependency-hashes.json').write_text(json.dumps(deps,indent=2)+'\n')
inputs={}
lanes=b.parent;camp=lanes.parent
paths=[root/'openai-proof-research/AGENTS.md',camp/'AGENTS.md',camp/'ledger.json',camp/'prior-campaign-context.json',root/'openai-proof-research/sources/upstream.json',root/'openai-proof-research/sources/CONTENTS.md',lanes/'root-cascade-rate-candidate-r1/PROOF.md',lanes/'root-cascade-formal-r1/ADOPTION.md',lanes/'sol-cascade-rate-preliminary-review-r1/review.md',lanes/'sol-cascade-source-prior-review-r2/review.md',lanes/'sol-cascade-source-tree-formal-r1/SUMMARY.md']
for p in paths:inputs[str(p)]=sha(p)
(b/'input-hashes.json').write_text(json.dumps(inputs,indent=2)+'\n')
audit=next((b/'replay/verification').glob('Audit*.log'));txt=audit.read_text();assert txt==(b/'verification/Audit-1793260721625949384.log').read_text()
entries=re.findall(r'^AUDIT (\S+) (\S+)',txt,re.M);assert len(entries)==206
assert 'unsafe=true' not in txt and 'axiom=true' not in txt
sources={str(p.relative_to(b)):sha(p) for p in (b/'formal').iterdir() if p.suffix=='.lean' or p.name=='run_lean.py'}
for p in (b/'replay/formal').glob('*.lean'):assert sha(p)==sha(b/'formal'/p.name)
failures=[]
for p in sorted((b/'verification').glob('receipt*.json')):
 for r in json.loads(p.read_text()):
  if r['exit']!=0:failures.append(r)
receipt=json.loads(next((b/'replay/verification').glob('receipt*.json')).read_text());assert all(r['exit']==0 and r['process_group_peak_RSS']<3*1024**3 for r in receipt)
info=dict(status='component formal PASS; not acceptance',credit=0,additional_count=3,total_count=33,lean_sha256=sha(leanroot/'bin/lean'),mathlib_revision_supplied='d13f23b723b8a846827a245b89c10fc7d3f11612',revision_limit='User-supplied revision metadata; no git operations. Exact used artifacts hashed.',source_hashes=sources,imported_modules=4146,dependency_artifacts=len(deps),audit_count=206,audit_module_counts={m:sum(x==m for x,_ in entries) for m in set(x for x,_ in entries)},audit_sha256=sha(audit),fresh_peak_RSS=max(r['process_group_peak_RSS'] for r in receipt),failures=failures,diagnostics='No mathematical numerical diagnostics; only bounded hash/audit bookkeeping.',provenance_seconds=time.monotonic()-start)
(b/'provenance.json').write_text(json.dumps(info,indent=2)+'\n');print(json.dumps(info,indent=2))
