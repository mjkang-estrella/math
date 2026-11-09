import urllib.request,json,zipfile,hashlib,sys
from pathlib import Path
P=Path(__file__).resolve().parents[1];D=P/'.deps';D.mkdir(exist_ok=True)
for name in ['reportlab','pillow','charset-normalizer']:
 info=json.load(urllib.request.urlopen('https://pypi.org/pypi/'+name+'/json'))
 wh=[x for x in info['urls'] if x['filename'].endswith('py3-none-any.whl')]
 if not wh:
  wh=[x for x in info['urls'] if 'cp315' in x['filename'] and 'x86_64' in x['filename'] and 'manylinux' in x['filename']]
 if not wh:
  print('NO WHEEL',name);continue
 x=wh[0];data=urllib.request.urlopen(x['url']).read();assert hashlib.sha256(data).hexdigest()==x['digests']['sha256']
 q=P/'tmp'/x['filename'];q.write_bytes(data)
 with zipfile.ZipFile(q) as z:z.extractall(D)
 print(name,x['filename'])
