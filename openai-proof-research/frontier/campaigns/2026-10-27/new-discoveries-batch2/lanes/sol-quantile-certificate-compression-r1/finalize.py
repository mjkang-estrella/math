from pathlib import Path
import hashlib,json,datetime
L=Path(__file__).resolve().parent
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
rows=json.loads((L/'freeze.json').read_text())
for row in rows:
 row['sha256_original_after']=sha(Path(row['original']))
 row['sha256_copy_after']=sha(L/row['copy'])
 assert row['sha256_before']==row['sha256_original_after']==row['sha256_copy_after']
(L/'scientific-hashes.json').write_text(json.dumps({'status':'PASS','scientific_files':rows},indent=2)+'\n')
for name in ['ledger.json','prior-campaign-context.json']:
 d=json.loads((L/'administrative'/name).read_text())
 print(name, 'note:',d.get('note',d.get('counting_standard')))
 for key,items in d.items():
  if isinstance(items,list):
   for item in items:
    if 'quantile' in json.dumps(item).lower(): print(key,json.dumps(item))
manifest={str(p.relative_to(L)):sha(p) for p in sorted(L.rglob('*')) if p.is_file() and p.name not in ['manifest.json','verification-receipt.json']}
(L/'manifest.json').write_text(json.dumps({'algorithm':'sha256','excluded':['manifest.json','verification-receipt.json'],'files':manifest},indent=2)+'\n')
print('manifest files',len(manifest),'scientific originals/copies',len(rows))
