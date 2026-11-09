"""Offline artifact verification; not a mathematical theorem certificate."""
import hashlib,json,pathlib
L=pathlib.Path(__file__).resolve().parents[1]
p=json.loads((L/'provenance.json').read_text())
for r in p['frozen_lane_sources']:
 b=(L/r['path']).read_bytes()
 assert len(b)==r['bytes'] and hashlib.sha256(b).hexdigest()==r['sha256'],r['path']
for r in p['receipts']:
 if 'path' in r:assert hashlib.sha256((L/r['path']).read_bytes()).hexdigest()==r['sha256']
expected={'omega-Problems-tree.json':1531,'omega-D5-tree.json':12430,'omega-Blueprint-tree.json':22996,'openai-preprints-tree.json':13578}
for f,n in expected.items():
 j=json.loads((L/'sources'/f).read_text());assert j['truncated'] is False and len(j['tree'])==n
 d=json.loads((L/'registry-delta.json').read_text())[f];assert not d['changed'] and d['new_entries']==n
assert 'Conjecture 2.' in (L/'sources/2309.02047v2.txt').read_text()
assert p['credit']==0 and p['formal_status'].startswith('NOT ATTEMPTED')
print('PASS: 16 source hashes, HTTP body hashes, complete registry tree counts, source label; no full theorem certification')
