from pathlib import Path
import json,hashlib,datetime
L=Path(__file__).resolve().parent
def digest(p):return hashlib.sha256(p.read_bytes()).hexdigest()
fail=json.loads((L/'failures.json').read_text())
if not any(x.get('stage')=='date-query' for x in fail):
 fail.append(dict(stage='date-query',error='First 2023 API date upper bound was mistyped 2312312359; response returned recent2026 hits.',repair='Preserved breadth-2023.xml; made a distinct corrected-range query. No access denial or retry/bypass.',scientific_use='Malformed-query hits not used for eight-body screening.'))
(L/'failures.json').write_text(json.dumps(fail,indent=2)+'\n')
src=[dict(file=str(p.relative_to(L)),sha256=digest(p),size=p.stat().st_size) for p in sorted((L/'sources').iterdir()) if p.is_file()]
(L/'source-bindings.json').write_text(json.dumps(src,indent=2)+'\n')
assert digest(L/'sources/ugolini-live-v2.pdf')==digest(L/'frozen/0032-1609.01133v2.pdf')
prov=dict(date=datetime.datetime.now(datetime.timezone.utc).isoformat(),scope='research lane only; credit0; no proof endpoint',counts=dict(additional=9,total=39,next=40),primary='https://arxiv.org/pdf/1609.01133v2',primary_sha256=digest(L/'sources/ugolini-live-v2.pdf'),custody='Original r293 and disposition scientific files flat-copied and hashed before reading. Admin snapshots initially viewed before their freeze; no pre-read custody asserted for that administrative view. New retrieval/text digests recorded before inspection.',limits='No complete current registry body coverage; older breadth originals unread; no prior-art clearance. All10 supports remain symbolically unclosed.',forbidden_routes_used=False,resource_caps=dict(AS_bytes=512*1024*1024,group_RSS_bytes=512*1024*1024,CPU_seconds=210,wall_seconds=230),verification='separate guarded verify.py after manifest')
(L/'provenance.json').write_text(json.dumps(prov,indent=2)+'\n')
files=[p for p in sorted(L.rglob('*')) if p.is_file() and p.name not in ['manifest.json','verification-receipt.json']]
manifest=dict(excludes=['manifest.json','verification-receipt.json'],files=[dict(path=str(p.relative_to(L)),sha256=digest(p),size=p.stat().st_size) for p in files])
(L/'manifest.json').write_text(json.dumps(manifest,indent=2)+'\n');print('manifest files',len(files))
