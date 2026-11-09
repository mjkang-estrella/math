from pathlib import Path
import json,hashlib,datetime
L=Path(__file__).resolve().parent
def sha(d):return hashlib.sha256(d).hexdigest()
m=json.loads((L/'MANIFEST.json').read_text());bad=[]
actual={str(p.relative_to(L))for p in L.rglob('*')if p.is_file()and p.name not in ['MANIFEST.json','verification-receipt.json']}
assert actual==set(m)
for name,h in m.items():
 p=L/name;d=p.read_bytes()
 if sha(d)!=h['sha256']or len(d)!=h['bytes']:bad.append(name)
refs=json.loads((L/'referenced-originals.json').read_text());changed=[]
for name,h in refs.items():
 p=Path(name)
 if not p.is_file()or sha(p.read_bytes())!=h['sha256']:changed.append(name)
receipt={'time_utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'separate_guarded_process':True,'manifest_sha256':sha((L/'MANIFEST.json').read_bytes()),'lane_files_checked':len(m),'lane_file_failures':bad,'scientific_originals_checked':len(refs),'changed_or_missing_originals':changed,'result':'PASS'if not bad and not changed else 'FAIL','no_full_endpoint_or_novelty_certification':True}
(L/'verification-receipt.json').write_text(json.dumps(receipt,indent=2));print(json.dumps(receipt));assert not bad and not changed
