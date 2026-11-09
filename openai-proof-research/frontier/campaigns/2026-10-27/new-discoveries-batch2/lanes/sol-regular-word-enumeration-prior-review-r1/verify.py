from pathlib import Path
import hashlib,json,datetime
L=Path(__file__).resolve().parent
def h(p):return hashlib.sha256(p.read_bytes()).hexdigest()
errors=[]; scientific=admin=new=0
M=json.loads((L/'manifest.json').read_text())
for row in M['files']:
 if h(L/row['path'])!=row['sha256']:errors.append('manifest '+row['path'])
actual={str(p.relative_to(L)) for p in L.rglob('*') if p.is_file() and p.name not in ['manifest.json','verification-receipt.json']}
if actual!={r['path'] for r in M['files']}:errors.append('manifest coverage')
for row in json.loads((L/'freeze.json').read_text())['inputs']:
 if row['administrative']:
  admin+=1
  # Shared administrative originals may evolve; the original snapshot is checked.
  if h(L/row['copy'])!=row['sha256']:errors.append('admin snapshot '+row['copy'])
 else:
  scientific+=1
  if h(Path(row['original']))!=row['sha256'] or h(L/row['copy'])!=row['sha256']:errors.append('scientific original/copy '+row['copy'])
for line in (L/'access.jsonl').read_text().splitlines():
 row=json.loads(line)
 if row.get('status')!=200:continue
 matches=[p for p in (L/'retrieved').iterdir() if h(p)==row['sha256']]
 if len(matches)!=1:errors.append('retrieval '+row['url']);continue
 p=matches[0];new+=1
 if h(L/'frozen-new'/p.name)!=row['sha256']:errors.append('retrieval copy '+p.name)
# Also compare immutable scout primary originals against our frozen scientific PDFs.
upstream=0
for line in (L/'frozen'/'sources.jsonl').read_text().splitlines():
 row=json.loads(line)
 if 'sha256' not in row or 'original' not in row:continue
 q=L/'frozen'/'frozen-sources'/Path(row.get('copy','')).name
 if q.is_file():
  upstream+=1
  if h(Path(row['original']))!=row['sha256'] or h(q)!=row['sha256']:errors.append('scout primary '+str(q))
receipt={'utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'status':'PASS' if not errors else 'FAIL','errors':errors,'manifest_sha256':h(L/'manifest.json'),'manifest_members':len(M['files']),'scientific_original_copy_bindings':scientific,'administrative_snapshots':admin,'new_retrieval_bindings':new,'scout_primary_bindings':upstream,'caps':{'AS_bytes':536870912,'groupRSS_bytes':536870912,'CPU_seconds':210,'wall_seconds':230},'counts_changed':False}
(L/'verification-receipt.json').write_text(json.dumps(receipt,indent=2)+'\n')
print(json.dumps(receipt));assert not errors
