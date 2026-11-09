from pathlib import Path
import json,hashlib,shutil,tarfile
L=Path(__file__).resolve().parent
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
rows=json.loads((L/'bindings.json').read_text())
for r in rows:assert sha(Path(r['original']))==sha(L/r['copy'])==r['sha256']
cov=json.loads((L/'frozen/sol-floor-sums-source-prior-review-r2/exactcoverage.json').read_text())
for b in cov['bodies']:
 for kind in ['pdf','text']:
  p=L.parent/'sol-floor-sums-source-prior-review-r2'/b[kind+'_path'];q=L/'sources'/p.name;q.parent.mkdir(exist_ok=True)
  assert sha(p)==b[kind+'_sha256'];shutil.copyfile(p,q);assert sha(q)==sha(p)
  rows.append(dict(original=str(p),copy=str(q.relative_to(L)),sha256=sha(p)))
# Bind query and certificate directly; do not duplicate the historical directory tree.
C=L.parent/'sol-floor-sums-certificate-r2'
for rel in ['dag.jsonl','dag-index.json','query-map.json','frozen/all-m-query.smt2','frozen/z3-proof.sexpr']:
 p=C/rel;q=L/'certificate'/p.name;q.parent.mkdir(exist_ok=True);h=sha(p);shutil.copyfile(p,q);assert sha(p)==sha(q)==h
 rows.append(dict(original=str(p),copy=str(q.relative_to(L)),sha256=h))
(L/'bindings.json').write_text(json.dumps(rows,indent=2)+'\n')
G=L.parent/'sol-edge-irregulator-manuscript-packet-r1/packet/helper_guard.py'
shutil.copyfile(G,L/'packet/helper_guard.py')
p=L/'packet/replay.sh';s=p.read_text();s=s.replace('G='+str(G),'G="${HELPER_GUARD:-$PWD/helper_guard.py}"');p.write_text(s)
with tarfile.open(L/'frozen/input/source-only.tar.gz') as t:
 for m in t.getmembers():
  if m.name.endswith('.lean'):assert hashlib.sha256(t.extractfile(m).read()).hexdigest()==sha(L/'packet'/m.name)
shutil.copytree(L/'packet',L/'replay')
print('prepared fresh replay; mathematical source bytes unchanged')
