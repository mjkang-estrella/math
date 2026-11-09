from pathlib import Path
import hashlib,json,zipfile,shutil
O=Path(__file__).resolve().parents[1]
H=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
shutil.copyfile(O/'receipts/resources.jsonl',O/'receipts/resources-prepackaging.jsonl')
def selected(p):
 rel=p.relative_to(O)
 return p.is_file() and not any(x.startswith('packet-safe-test') or x=='tmp' for x in rel.parts) and str(rel) not in ['MANIFEST.sha256','dossier.zip','archive-receipt.json','receipts/resources.jsonl']
files=sorted(p for p in O.rglob('*') if selected(p))
manifest={str(p.relative_to(O)):H(p) for p in files}
(O/'MANIFEST.sha256').write_text(''.join(f'{h}  {n}\n' for n,h in manifest.items()))
with zipfile.ZipFile(O/'dossier.zip','w',zipfile.ZIP_DEFLATED,compresslevel=6) as z:
 for p in files+[O/'MANIFEST.sha256']:z.write(p,str(p.relative_to(O)))
with zipfile.ZipFile(O/'dossier.zip') as z:
 assert z.testzip() is None
 for n,h in manifest.items():assert hashlib.sha256(z.read(n)).hexdigest()==h
 assert z.read('lean-source.zip')==(O/'lean-source.zip').read_bytes()
rec={'status':'PASS','archive':'dossier.zip','sha256':H(O/'dossier.zip'),'bytes':(O/'dossier.zip').stat().st_size,'manifest_sha256':H(O/'MANIFEST.sha256'),'payload_files':len(files)+1,'zip_CRC_and_every_manifest_hash_verified':True,'inner_lean_packet_byte_identical':True,'exclusions':['scratch packet-safe-test* directories','tmp/','live receipts/resources.jsonl','external archive-receipt.json','archive self']}
(O/'archive-receipt.json').write_text(json.dumps(rec,indent=2)+'\n')
for n,h in manifest.items():assert H(O/n)==h
print(json.dumps(rec,indent=2))
