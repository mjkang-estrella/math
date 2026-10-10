from pathlib import Path
import json,urllib.request,urllib.error,hashlib,datetime,subprocess,concurrent.futures
S=Path('frontier/sources/i58_standard_map_additive_entropy_novelty')
def dump(p,d):p.write_text(json.dumps(d,indent=2)+'\n')
p=S/'corpus-inventory.json';d=json.loads(p.read_text());tree=json.loads(Path('sources/preprints-tree.json').read_text())['tree'];d['manuscripts']=len({x['path'].split('/')[1] for x in tree});assert d['manuscripts']==749;dump(p,d)
p=Path('frontier/experiments/i58_standard_map_additive_entropy_novelty/prepare.py');p.write_text(p.read_text().replace("x['path'].split('/')[0]", "x['path'].split('/')[1]"))
with (S/'process-notes.txt').open('a') as f:f.write('Initial inventory manuscript count was 1 because preprints/ was counted instead of its child manuscript directory. Corrected to tree path component 1, independently asserted 749; corpus blob checks were already valid.\n')
requests=[('bloor-current','https://arxiv.org/abs/0810.3122','html'),('bloor-v1','https://arxiv.org/pdf/0810.3122v1','pdf'),('holland-current','https://arxiv.org/abs/math/0502236','html'),('holland-v1','https://arxiv.org/pdf/math/0502236v1','pdf')]
def fetch(x):
 n,u,ext=x;rec={'name':n,'url':u,'path':f'literature/{n}.{ext}','retrieved':datetime.datetime.now(datetime.timezone.utc).isoformat()}
 try:
  with urllib.request.urlopen(urllib.request.Request(u,headers={'User-Agent':'Mozilla/5.0'}),timeout=40) as f:b=f.read();rec.update(status=f.status,final_url=f.url,content_type=f.headers.get('Content-Type'))
 except urllib.error.HTTPError as e:b=e.read();rec.update(status=e.code,error=str(e))
 except Exception as e:b=str(e).encode();rec.update(status=None,error=str(e))
 (S/rec['path']).write_bytes(b);rec['sha256']=hashlib.sha256(b).hexdigest();return rec
with concurrent.futures.ThreadPoolExecutor(max_workers=4) as ex:rs=list(ex.map(fetch,requests))
dump(S/'extra-responses.json',rs)
pdfs=[]
for r in rs:
 if r['path'].endswith('.pdf') and (S/r['path']).read_bytes().startswith(b'%PDF'):
  b=subprocess.check_output(['pdftotext','-layout',str(S/r['path']),'-']);p=r['path'][:-4]+'.txt';(S/p).write_bytes(b);pdfs.append({'pdf':r['path'],'text':p,'sha256':hashlib.sha256(b).hexdigest()})
dump(S/'extra-pdf-extractions.json',pdfs)
print([(x['name'],x['status']) for x in rs])
