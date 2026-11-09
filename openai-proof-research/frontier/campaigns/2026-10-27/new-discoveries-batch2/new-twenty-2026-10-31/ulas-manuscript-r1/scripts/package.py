from pathlib import Path
import json,hashlib,zipfile,datetime
r=Path(__file__).resolve().parents[1]
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
# Inspect the packet only; do not execute any archived tool.
with zipfile.ZipFile(r/'ulas-source.zip') as z:
 names=z.namelist()
 assert len([n for n in names if n.startswith('src/') and n.endswith('.lean')])==43
 assert not any(Path(n).suffix in ['.olean','.ilean','.o','.c','.so'] for n in names)
 assert z.testzip() is None
for name in ['frozen-inputs','supplemental-inputs','renderer-inputs']:
 before=json.loads((r/(name+'-before.json')).read_text());after=json.loads((r/(name+'-after.json')).read_text());assert before==after
 assert all(sha((next(p for p in r.parents if p.name=='math')/p) if not Path(p).is_absolute() else Path(p))==h for p,h in before.items())
q=json.loads((r/'qa/receipt.json').read_text());assert q['pdf_sha256']==sha(r/'paper.pdf')
assert all(sha(r/'qa'/p)==h for p,h in q['images'].items())
# All completion receipts already available enter this snapshot; the packager's own receipt follows it.
exclude={'ulas-full-dossier.zip','DOSSIER-MANIFEST.json','DELIVERY.json','receipts/package-final.json','receipts/delivery-validation.json'}
files=[p for p in r.rglob('*') if p.is_file() and str(p.relative_to(r)) not in exclude and 'safe-extraction' not in p.relative_to(r).parts and '__pycache__' not in p.relative_to(r).parts and p.suffix!='.pyc']
manifest={str(p.relative_to(r)):dict(sha256=sha(p),bytes=p.stat().st_size) for p in sorted(files)}
(r/'DOSSIER-MANIFEST.json').write_text(json.dumps(dict(schema=1,scope='ZIP snapshot excluding redundant extraction, bytecode caches, self, ZIP and post-packaging receipts',files=manifest),indent=2)+'\n')
with zipfile.ZipFile(r/'ulas-full-dossier.zip','w',compression=zipfile.ZIP_DEFLATED,compresslevel=6) as z:
 for p in sorted(files)+[r/'DOSSIER-MANIFEST.json']:z.write(p,str(p.relative_to(r)))
with zipfile.ZipFile(r/'ulas-full-dossier.zip') as z:
 assert z.testzip() is None
 for p,v in manifest.items():assert hashlib.sha256(z.read(p)).hexdigest()==v['sha256']
 assert z.read('ulas-source.zip')==(r/'ulas-source.zip').read_bytes()
(r/'DELIVERY.json').write_text(json.dumps(dict(utc=datetime.datetime.now(datetime.timezone.utc).isoformat(),artifacts={n:dict(sha256=sha(r/n),bytes=(r/n).stat().st_size) for n in ['paper.pdf','paper.md','ulas-source.zip','ulas-full-dossier.zip','DOSSIER-MANIFEST.json']},zip_crc_ok=True,all_snapshot_member_hashes_verified=True,source_zip_byte_identical=True,accepted_credit=0),indent=2)+'\n')
print('Full dossier ZIP CRC and every member hash verified:',len(manifest)+1,'members')
print('ZIP SHA-256',sha(r/'ulas-full-dossier.zip'))
