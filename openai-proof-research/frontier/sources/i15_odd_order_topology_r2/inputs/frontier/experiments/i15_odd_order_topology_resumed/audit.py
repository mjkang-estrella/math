#!/usr/bin/env python3
"""Read-only dependency checks; writes only the resumed audit result."""
import hashlib,json,re
from pathlib import Path
ROOT=Path(__file__).resolve().parents[3]
OUT=ROOT/'frontier/sources/i15_odd_order_topology_resumed'
OLD=ROOT/'frontier/sources/i15_odd_order_topology'
def sha(b): return hashlib.sha256(b).hexdigest()
def record(p):
 b=p.read_bytes();return dict(path=str(p.relative_to(ROOT)),bytes=len(b),sha256=sha(b))
snapshot=OUT/'inputs/frontier/iterations/pause-at-four-artifact-snapshot.json'
rows=[x for x in json.loads(snapshot.read_text())['files'] if 'i15' in x['path']]
for x in rows: assert record(ROOT/x['path'])==x,x['path']
actual={str(p.relative_to(ROOT)) for d in [OLD,ROOT/'frontier/experiments/i15_odd_order_topology'] for p in d.rglob('*') if p.is_file()}
actual.add('frontier/iterations/i15-odd-order-topology.md')
assert actual=={x['path'] for x in rows}
t=json.loads((OLD/'inputs/sources/preprints-tree.json').read_text()); assert not t['truncated']
idx={x['path']:x for x in t['tree']};assert len(idx)==len(t['tree'])
pin='fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb'
manifest=json.loads((OLD/'pinned-manifest.json').read_text())
for x in manifest:
 p=OLD/'upstream'/x['path'];b=p.read_bytes()
 assert sha(b)==x['sha256'] and len(b)==x['bytes']
 assert hashlib.sha1(b'blob '+str(len(b)).encode()+b'\0'+b).hexdigest()==idx[x['path']]['sha']==x['git_blob_sha1']
 assert x['url']=='https://raw.githubusercontent.com/openai/math/'+pin+'/'+x['path']
contracts=json.loads((OLD/'contracts.json').read_text())
for x in contracts:
 b=(OLD/'upstream'/x['path']).read_bytes();s=b.decode();statement='\n'.join(s.splitlines()[x['start_line']-1:x['end_line']])
 assert sha(b)==x['source_sha256']
 assert statement==x['statement'] and sha(statement.encode())==x['statement_sha256'],x['labels']
 for lab in x['labels']: assert '\\label{'+lab+'}' in statement
literature=[]
for name in ['retained','new','final']:
 for x in json.loads((OLD/'literature'/f'{name}-manifest.json').read_text()):
  for ext,key in [('pdf','sha256'),('txt','text_sha256')]:
   p=OLD/'literature'/(x['name']+'.'+ext);assert sha(p.read_bytes())==x[key]
  literature.append(x['name'])
# Every saved JSON evidence record is syntactically valid, including search replies.
json_files=list(OLD.rglob('*.json'))
for p in json_files:json.loads(p.read_text())
new_retrievals=[]
for name in ['retrieval-manifest.json','additional-retrieval-manifest.json','final-retrieval-manifest.json']:
 for x in json.loads((OUT/name).read_text()):
  if 'error' in x:continue
  p=OUT/x['path'];b=p.read_bytes()
  assert sha(b)==x['sha256'] and len(b)==x['bytes'], x['path']
  if 'text_path' in x:assert sha((OUT/x['text_path']).read_bytes())==x['text_sha256']
  if x['path'].startswith('upstream/'):
   assert b==(OLD/x['path']).read_bytes(), x['path']
  new_retrievals.append(x['path'])
reading=json.loads((OUT/'reading-index.json').read_text())['records']
for x in reading:
 for ext in ['pdf','text']:
  assert sha((ROOT/x[ext+'_path']).read_bytes())==x[ext+'_sha256']
 lines=(ROOT/x['text_path']).read_text().splitlines()
 for e in x['passages']:
  passage='\n'.join(lines[e['start_line']-1:e['end_line']])
  assert passage==e['text'] and sha(passage.encode())==e['sha256']
report=ROOT/'frontier/iterations/i15-odd-order-topology-resumed.md'
text=report.read_text()
assert not any(ord(c)<32 and c!='\n' for c in text), 'Control character in report'
for destination in re.findall(r'\]\(([^)]+)\)',text):
 if not destination.startswith(('https://','http://','#')):
  assert (report.parent/destination).exists(), destination
assert text.count('\\[')==text.count('\\]')
assert text.count('\\(')==text.count('\\)')
result=dict(status='PASS: artifact/source identities, not proof acceptance',old_artifacts=len(rows),deviations=[],pinned_files=len(manifest),contracts=len(contracts),literature_pairs=len(literature),json_files=len(json_files),tree_entries=len(idx),tree_blobs=sum(x['type']=='blob' for x in idx.values()),missing_old_claimed_artifacts=['seal.py','reading-index.json'],pin=pin,dependencies=rows)
result.update(successful_new_retrievals=len(new_retrievals),primary_reading_records=len(reading),exact_primary_passages=sum(len(x['passages']) for x in reading),report_local_links_and_math_delimiters='PASS')
(OUT/'audit-results.json').write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps({k:v for k,v in result.items() if k!='dependencies'}))
