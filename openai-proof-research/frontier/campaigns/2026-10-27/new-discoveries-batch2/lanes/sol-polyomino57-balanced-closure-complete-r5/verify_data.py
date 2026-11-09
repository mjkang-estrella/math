from pathlib import Path
import json,hashlib,resource,signal
resource.setrlimit(resource.RLIMIT_AS,(512*1024**2,)*2);resource.setrlimit(resource.RLIMIT_CPU,(30,35));signal.alarm(45)
L=Path(__file__).resolve().parent;R=L.parent/'sol-polyomino57-full-closure-formal-r4';checks={}
for archive,receipt in [('closure-path-data.zip','closure-path-archive.json'),('terminal-map-data.zip','terminal-map-archive.json')]:
 h=hashlib.file_digest((R/archive).open('rb'),'sha256').hexdigest();assert h==json.loads((R/receipt).read_text())['sha256'];checks[archive]=h
for e in json.loads((R/'closure-path-data-receipt.json').read_text())['stages']:
 p=L/'closure-path-data'/('closure%d.jsonl'%e['source_size']);assert hashlib.file_digest(p.open('rb'),'sha256').hexdigest()==e['sha256']
p=R/'terminal-correspondence.jsonl';assert hashlib.file_digest(p.open('rb'),'sha256').hexdigest()==json.loads((R/'terminal-map-receipt.json').read_text())['sha256']
(L/'data-input-hashes.json').write_text(json.dumps(checks,indent=2)+'\n')
import zipfile
for archive in ['closure-path-data.zip','terminal-map-data.zip']:
 with zipfile.ZipFile(R/archive) as z:
  for name in z.namelist():
   if name.startswith('closure-path-data/') or name in ['closure-path-data-receipt.json','terminal-correspondence.jsonl','terminal-map-receipt.json']:
    p=L/name if name.startswith('closure-path-data/') else R/name
    assert hashlib.sha256(z.read(name)).hexdigest()==hashlib.file_digest(p.open('rb'),'sha256').hexdigest(),name
