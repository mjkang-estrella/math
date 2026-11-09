from pathlib import Path
import hashlib,json
L=Path(__file__).resolve().parent
target='6f5dda75ff8a62da937411d1e2da1d5164b1439ce6a0143118b7c70dda6070cc'
for line in (L/'citers.log').read_bytes().splitlines(keepends=True):
 for data in [line,line.rstrip(b'\r\n')]:
  if hashlib.sha256(data).hexdigest()==target:
   p=L/'sources/juras-published-record-citers-recovered.json';p.write_bytes(data)
   assert hashlib.sha256(p.read_bytes()).hexdigest()==target
   (L/'recovery.json').write_text(json.dumps({target:str(p)},indent=2))
   print('RECOVERED original 13985 bytes with identical SHA256; no re-fetch');raise SystemExit(0)
raise SystemExit('FAILED exact byte recovery')
