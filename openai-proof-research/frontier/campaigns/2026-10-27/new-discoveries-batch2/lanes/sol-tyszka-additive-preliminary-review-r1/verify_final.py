from pathlib import Path
import datetime,hashlib,json
O=Path(__file__).resolve().parent
h=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
m=json.loads((O/'finalmanifest.json').read_text())
assert set(m['explicit_exclusions'])=={'finalmanifest.json','verification-receipt.json'}
actual={str(p.relative_to(O)) for p in O.rglob('*') if p.is_file()}-set(m['explicit_exclusions'])
assert actual==set(m['files'])
for p,v in m['files'].items():assert h(O/p)==v,p
f=json.loads((O/'input-freeze.json').read_text())
for r in f['scientific']:
    assert h(Path(r['original']))==r['sha256'],r['original']
    assert h(O/r['copy'])==r['sha256'],r['copy']
    assert (O/r['copy']).stat().st_mode & 0o222==0
receipt={'utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'status':'PASS','manifest_sha256':h(O/'finalmanifest.json'),'manifest_payload_files':len(m['files']),'originals_and_readonly_copies_verified':len(f['scientific']),'explicit_manifest_exclusions':m['explicit_exclusions'],'scope':'Byte integrity and original/copy preservation only; not a proof or novelty certification. Separate guarded verification after final writes.'}
(O/'verification-receipt.json').write_text(json.dumps(receipt,indent=2)+'\n')
print(json.dumps(receipt))
