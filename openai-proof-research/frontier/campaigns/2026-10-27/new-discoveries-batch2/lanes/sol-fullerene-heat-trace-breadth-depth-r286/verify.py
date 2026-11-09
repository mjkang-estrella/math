from pathlib import Path
import json,hashlib,subprocess,sys,datetime
L=Path(__file__).resolve().parent
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
manifest=json.loads((L/'MANIFEST.json').read_text());assert 'MANIFEST.json' not in manifest and 'verification-receipt.json' not in manifest
assert set(manifest)=={str(p.relative_to(L)) for p in L.rglob('*') if p.is_file() and p.name not in ['MANIFEST.json','verification-receipt.json']}
for name,r in manifest.items():p=L/name;assert sha(p)==r['sha256'] and p.stat().st_size==r['bytes'],name
scientific=0
for row in json.loads((L/'freeze.json').read_text()):
 assert sha(Path(row['copy']))==row['sha256']
 if row['kind']=='scientific frozen':assert sha(Path(row['original']))==row['sha256'];scientific+=1
for line in (L/'bindings.jsonl').read_text().splitlines():
 r=json.loads(line);p=L/r['path'];assert sha(p)==r['sha256'],str(p)
 if r.get('original'):
  q=Path(r['original'])
  if r['path'].startswith('frozen/ref-'):
   assert sha(q)==r['sha256'],str(q);scientific+=1
  else:
   # Extraction/transcription is a derivation, not an identical copy.
   # Its archive/PDF origin must itself be present and hash-bound.
   rel=str(q.relative_to(L));assert rel in manifest;assert sha(q)==manifest[rel]['sha256']
r=subprocess.run([sys.executable,str(L/'independent_check.py')],capture_output=True,text=True,check=True)
receipt=dict(status='PASS',time=datetime.datetime.now(datetime.timezone.utc).isoformat(),manifest_sha256=sha(L/'MANIFEST.json'),files=len(manifest),original_copy_scientific_checks=scientific,administrative='snapshot hashes only; no assertion about live ledger after snapshot',independent_check=json.loads(r.stdout),credit=0,limits='unchanged required external helper_guard: AS/groupRSS512MiB CPU210 wall230')
(L/'verification-receipt.json').write_text(json.dumps(receipt,indent=2));print(json.dumps(receipt))
