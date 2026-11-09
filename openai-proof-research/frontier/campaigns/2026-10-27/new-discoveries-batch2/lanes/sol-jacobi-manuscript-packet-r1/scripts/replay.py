#!/usr/bin/env python3
"""Fresh own extraction; immutable payload and external receipt, no circular hash."""
import hashlib,json,os,subprocess,sys,zipfile
from pathlib import Path
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
packet=Path(sys.argv[1]).resolve(); dest=Path(sys.argv[2]).resolve();assert not dest.exists()
dest.mkdir(parents=True); payload=dest/'payload';payload.mkdir()
with zipfile.ZipFile(packet) as z:
 names=z.namelist();assert len(names)==len(set(names));assert names==sorted(names)
 assert all(not Path(n).is_absolute() and '..' not in Path(n).parts and not n.endswith(('.olean','.ilean','.ir','.o','.so','.pyc')) for n in names)
 z.extractall(payload)
manifest=json.loads((payload/'manifest.json').read_text());assert set(names)==set(manifest)|{'manifest.json'}
def verify():
 for n,h in manifest.items():assert sha(payload/n)==h,n
verify()
env=dict(os.environ);env['PYTHONDONTWRITEBYTECODE']='1'
with (dest/'replay-driver.log').open('wb') as out:
 p=subprocess.run([sys.executable,str(payload/'scripts/verify.py'),str(payload),str(dest/'build')],cwd=payload,env=env,stdout=out,stderr=subprocess.STDOUT)
assert p.returncode==0,str(dest/'replay-driver.log')
verify(); receipt=json.loads((dest/'build/replay-receipt.json').read_text())
receipt.update(packet_sha256=sha(packet),payload_manifest_sha256=sha(payload/'manifest.json'),payload_hashes_before_after_verified=True,extraction_directory=str(dest),immutable_payload=True)
(dest/'extraction-receipt.json').write_text(json.dumps(receipt,indent=2)+'\n');print('PASS '+str(receipt['full_generated_origin_declaration_count'])+' declarations; packet '+sha(packet))
