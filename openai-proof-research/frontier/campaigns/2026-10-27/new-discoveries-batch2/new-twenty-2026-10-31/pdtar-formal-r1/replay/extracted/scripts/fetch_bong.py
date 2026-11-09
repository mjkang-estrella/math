import urllib.request, pathlib, json, hashlib, time
D=pathlib.Path(__file__).resolve().parents[1]
u='https://arxiv.org/html/2205.09668'
try:
 with urllib.request.urlopen(u,timeout=30) as r:
  b=r.read(); status=r.status
except urllib.error.HTTPError as e:
 status=e.code; b=e.read()
except Exception as e:
 status=str(e); b=b''
(D/'logs/bong-body-response').write_bytes(b)
(D/'logs/bong-receipt.json').write_text(json.dumps(dict(url=u,status=status,sha256=hashlib.sha256(b).hexdigest(),utc=time.strftime('%Y-%m-%dT%H:%M:%SZ',time.gmtime())),indent=2))
print(status,len(b))
