import datetime,hashlib,json,pathlib,urllib.request
L=pathlib.Path(__file__).resolve().parents[1]; records=[]
def get(name,url):
 r={'url':url,'utc':datetime.datetime.now(datetime.timezone.utc).isoformat()}
 try:
  with urllib.request.urlopen(urllib.request.Request(url,headers={'User-Agent':'Public mathematical research'}),timeout=40) as f:
   b=f.read();r.update(status=f.status,final_url=f.url)
  (L/'sources'/name).write_bytes(b);r.update(path='sources/'+name,sha256=hashlib.sha256(b).hexdigest(),bytes=len(b))
  records.append(r);return b
 except Exception as e:r['error']=str(e);records.append(r);return None
try:
 for prefix,repo in [('omega','the-omega-institute/trureturing'),('openai','openai/math')]:
  b=get(prefix+'-head.json','https://api.github.com/repos/'+repo+'/commits/HEAD')
  if not b:continue
  head=json.loads(b)['sha']; print(prefix,head,flush=True)
  root=get(prefix+'-root.json',f'https://api.github.com/repos/{repo}/git/trees/{head}')
  if not root:continue
  for t in json.loads(root)['tree']:
   if t['path'] in (['Problems','D5','Blueprint'] if prefix=='omega' else ['preprints']):
    get(prefix+'-'+t['path']+'-tree.json',f'https://api.github.com/repos/{repo}/git/trees/{t["sha"]}?recursive=1')
  if prefix=='openai':get('openai-CONTENTS.md',f'https://raw.githubusercontent.com/{repo}/{head}/CONTENTS.md')
 get('arxiv-abs.html','https://arxiv.org/abs/2309.02047')
 get('BMIGNP.pdf','https://people.tamu.edu/~terdelyi/papers-online/BMIGNP.pdf')
finally:
 (L/'retrieval.json').write_text(json.dumps(records,indent=2)+'\n')
