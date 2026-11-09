from pathlib import Path
import hashlib,json
L=Path('/home/mj-kang/Documents/Dev/math/openai-proof-research/frontier/campaigns/2026-10-27/new-discoveries-batch2/new-twenty-2026-10-31/splitmatch-review-r1');D=L.parent/'expanded-corpus-r168'
r=json.loads((D/'results.json').read_text())['381751'];raw=(D/'raw/381751.jsonl').read_bytes()
assert hashlib.sha256(raw).hexdigest()==r['provenance']['raw_sha256']
p=Path(r['provenance']['chunk']);h=hashlib.sha256()
with p.open('rb') as f:
 for i,line in enumerate(f,1):
  h.update(line)
  if i==785:assert line==raw
assert h.hexdigest()==r['provenance']['chunk_sha256']
assert hashlib.sha256(r['statement'].encode()).hexdigest()==r['provenance']['statement_utf8_sha256']
print('Raw, original chunk line 785, chunk hash, statement hash: PASS')
print('packet',hashlib.sha256((D/'Lean-packet.zip').read_bytes()).hexdigest())
for n in ['github-search1','github-search2','github-search3']:
 x=json.loads((L/'downloads'/n/'raw').read_text());print(n,x['total_count'],x.get('incomplete_results'))
x=json.loads((L/'downloads/openalex-arxiv-record/raw').read_text());print('Exact arxiv OpenAlex record filter',x['meta']['count'],[(y['id'],y['title']) for y in x['results']])
