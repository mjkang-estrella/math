import pathlib,json,urllib.request,hashlib
O=pathlib.Path(__file__).parent;u='https://aiproofwatch.com/problems'
try:
 with urllib.request.urlopen(u,timeout=20) as f:b=f.read(4000000)
 p=O/'primary/current-registry.html';p.write_bytes(b)
 r={'url':u,'file':str(p.relative_to(O)),'sha256':hashlib.sha256(b).hexdigest(),'size':len(b),'limit':'Landing page only; no complete exact-scope registry or current repository head established. No clearance.'}
except Exception as e:r={'url':u,'error':str(e),'limit':'Current registry unavailable; HOLD for any promotion.'}
(O/'registry-provenance.json').write_text(json.dumps(r,indent=2)+'\n');print(r)
