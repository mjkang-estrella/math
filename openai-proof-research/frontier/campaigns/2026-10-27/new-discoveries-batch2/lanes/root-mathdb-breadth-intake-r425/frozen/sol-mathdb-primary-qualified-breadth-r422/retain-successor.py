import pathlib,json,urllib.request,hashlib
O=pathlib.Path(__file__).parent;u='https://arxiv.org/html/math/0505315'
try:
 with urllib.request.urlopen(u,timeout=20) as f:b=f.read(5000000)
 p=O/'primary/adjoint.html';p.write_bytes(b)
 r={'url':u,'file':str(p.relative_to(O)),'sha256':hashlib.sha256(b).hexdigest(),'size':len(b),'read_sections':'2.5-2.14 through web body; even-size construction only'}
except Exception as e:r={'url':u,'error':str(e),'limit':'Web body inspected; local bytes unavailable. No retry.'}
(O/'retained-successor.json').write_text(json.dumps(r,indent=2)+'\n')
