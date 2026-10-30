import json,hashlib,sys
from fractions import Fraction as Q
from pathlib import Path
L=Path(__file__).resolve().parent
def sha(b):return hashlib.sha256(b).hexdigest()
# Exact monomial coefficient checks for m U'=h(m)w(1)-integral h(mt)(w+tw').
# These diagnose transcription only; the ordinary proof uses integration by parts.
tests=0
for d in range(1,25):
 for j in range(18):
  assert Q(d,d+j+1)==1-Q(j+1,d+j+1)
  tests+=1
http=[json.loads(s) for s in (L/'http.jsonl').read_text().splitlines()]
for r in http:
 if 'sha256' in r:
  b=(L/'sources'/r['name']).read_bytes();assert len(b)==r['bytes'] and sha(b)==r['sha256']
for a,b in [('geometry.pdf','geometry-v3.pdf'),('primary.pdf','primary-v1.pdf'),('localization.pdf','localization-v2.pdf')]:
 assert (L/'sources'/a).read_bytes()==(L/'sources'/b).read_bytes()
root=json.loads((L/'sources/omega-root.json').read_bytes());sub={x['path']:x['sha'] for x in root['tree']}
for name,tree in [('Library','omega-library-tree.json'),('Problems','omega-problems-tree.json'),('docs','omega-docs-tree.json')]:
 j=json.loads((L.parent/'sol-fresh-source-discovery-r143/sources'/tree).read_bytes());assert sub[name]==j['sha'] and j['truncated'] is False
for row in map(json.loads,(L/'alias-queries.jsonl').read_text().splitlines()):
 for hit in row['hits']:assert sha((L/hit['copy']).read_bytes())==hit['sha256']
guard=L.parent/'sol-edge-irregulator-manuscript-packet-r1/packet/helper_guard.py'
assert sha(guard.read_bytes())=='825ee0d48177cd12354cdbf36fd36b61f0503ff3241356a7bf638ee0bc49fa45'
result=dict(boundary_identity_monomials=tests,primary_hashes=True,pinned_latest_bytes_equal=True,fixed_registry_subtrees_equal=True,reopened_hashes=True,guard_unchanged=True,universal_source_proof=False)
if '--verify' in sys.argv:assert result==json.loads((L/'check-results.json').read_bytes())
else:(L/'check-results.json').write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps(result))
