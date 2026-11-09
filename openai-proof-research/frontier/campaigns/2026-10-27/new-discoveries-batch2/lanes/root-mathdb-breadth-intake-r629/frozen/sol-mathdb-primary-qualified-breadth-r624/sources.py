from pathlib import Path
import json,hashlib,urllib.request,datetime,subprocess
D=Path(__file__).resolve().parent;L=D.parent
refs=json.loads((D/'flat-bindings.json').read_text());log=[]
def bind(p,h=None,n=None):
 b=p.read_bytes();x={'path':str(p),'sha256':hashlib.sha256(b).hexdigest(),'size':len(b)}
 if h:assert x['sha256']==h
 if n:assert x['size']==n
 refs.append(x);return x
P=L/'sol-mathdb-primary-qualified-breadth-r400';bind(P/'manifest.json','d167070bf8ca40de6046ae6d3e46a287be73fc0ae2bc8f57dff12eef9e234ae6')
m=json.loads((P/'manifest.json').read_text())
for x in m['files']:
 if 'rbm-review' in x['path'] or x['path'] in ['source-provenance.json','source-coverage.json']:bind(P/x['path'],x['sha256'],x.get('size',x.get('bytes')))
url='https://arxiv.org/pdf/1610.07904v1';p=D/'critical-height-v1.pdf'
try:
 with urllib.request.urlopen(urllib.request.Request(url,headers={'User-Agent':'Python-urllib/3'}),timeout=35) as r:
  b=r.read(6000000);assert b.startswith(b'%PDF');p.write_bytes(b)
 x=bind(p);log.append({'url':url,'utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'status':200,**x})
 subprocess.run(['pdftotext','-layout',str(p),str(D/'critical-height-v1.txt')],check=True)
 bind(D/'critical-height-v1.txt')
except Exception as e:log.append({'url':url,'utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'failure':str(e),'retry':False})
(D/'flat-bindings.json').write_text(json.dumps(refs,indent=2)+'\n');(D/'source-provenance.json').write_text(json.dumps(log,indent=2)+'\n')
print(log)
