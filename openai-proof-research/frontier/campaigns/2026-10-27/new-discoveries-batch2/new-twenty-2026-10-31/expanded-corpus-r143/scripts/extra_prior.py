import urllib.request,json,pathlib,datetime,hashlib
head=json.load(open('outputs/registries.json'))['openai/math']['head'];paths=json.load(open('../fresh-corpus-r10/sources/registry-preprints.json'))['tree'];r=[]
for x in paths:
 if 'Elementary-Positivity' in x['path'] and x['path'].endswith('sections/01-introduction.tex'):
  u='https://raw.githubusercontent.com/openai/math/'+head+'/preprints/'+x['path'];p='sources/openai-elementary-introduction.tex'
  try:
   v=urllib.request.urlopen(u,timeout=15);b=v.read();pathlib.Path(p).write_bytes(b);r.append({'url':u,'status':v.status,'sha256':hashlib.sha256(b).hexdigest(),'utc':datetime.datetime.now(datetime.timezone.utc).isoformat()})
  except Exception as e:r.append({'url':u,'error':str(e)})
u='https://arxiv.org/pdf/2303.15756'
try:
 v=urllib.request.urlopen(u,timeout=15);b=v.read();pathlib.Path('sources/2303.15756.pdf').write_bytes(b);r.append({'url':u,'status':v.status,'sha256':hashlib.sha256(b).hexdigest(),'utc':datetime.datetime.now(datetime.timezone.utc).isoformat()})
except Exception as e:r.append({'url':u,'error':str(e)})
json.dump(r,open('outputs/extra-http.json','w'),indent=2)
