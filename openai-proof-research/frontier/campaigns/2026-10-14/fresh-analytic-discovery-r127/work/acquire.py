from pathlib import Path
import urllib.request,hashlib,json,concurrent.futures
root=Path(__file__).resolve().parents[1]; dest=root/'packet/private/upstream';commit='fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb'
rows=[]
for f in dest.glob('*-paths.json'):
 for x in json.loads(f.read_text()):
  if x['type']=='blob' and x['path'].endswith('.tex') and '/sections/' in x['path']:rows.append((f.name[:3],x))
def get(row):
 n,x=row;url='https://raw.githubusercontent.com/openai/math/'+commit+'/'+x['path'];b=urllib.request.urlopen(url,timeout=40).read();h=hashlib.sha1(b'blob '+str(len(b)).encode()+b'\0'+b).hexdigest();assert h==x['sha'];assert len(b)==x['size'];p=dest/n/Path(x['path']).parts[1]/Path(x['path']).name;p.parent.mkdir(parents=True,exist_ok=True);p.write_bytes(b);return dict(canonical=x,url=url,sha256=hashlib.sha256(b).hexdigest(),local=str(p.relative_to(root/'packet')),read='acquired only')
with concurrent.futures.ThreadPoolExecutor(max_workers=6) as ex:
 for x in ex.map(get,rows): print(x['local']);rows2=locals().setdefault('records',[]);rows2.append(x)
(dest/'register.json').write_text(json.dumps(records,indent=2)+'\n')
