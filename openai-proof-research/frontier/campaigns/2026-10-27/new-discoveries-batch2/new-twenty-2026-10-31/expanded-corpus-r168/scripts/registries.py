import pathlib,json,urllib.request,hashlib,datetime,re
D=pathlib.Path(__file__).resolve().parents[1];p=D/'sources/registries';p.mkdir(exist_ok=True);out=[]
def get(u,name):
 r={'url':u,'utc':datetime.datetime.now(datetime.timezone.utc).isoformat()}
 try:
  with urllib.request.urlopen(u,timeout=20) as f:b=f.read();r.update(status=f.status,sha256=hashlib.sha256(b).hexdigest());(p/name).write_bytes(b)
  obj=json.loads(b)
 except Exception as e:r['error']=str(e);obj={}
 out.append(r);(D/'outputs/registry-fetch.json').write_text(json.dumps(out,indent=2));return obj
for repo,label in [('the-omega-institute/trureturing','omega'),('openai/math','openai')]:
 sha=json.loads((D/'sources/extra'/f'{label}-head/raw').read_text())['sha'];tree=get(f'https://api.github.com/repos/{repo}/git/trees/{sha}',f'{label}-root.json')
 for x in tree.get('tree',[]):
  if x['path'] in ['D5','Problems','preprints']:
   get(f'https://api.github.com/repos/{repo}/git/trees/{x["sha"]}?recursive=1',f'{label}-{x["path"]}.json')
# Fetch additional primary bodies; never executes downloaded code.
for name,u in {'ballot-proof':'https://arxiv.org/pdf/2009.05973','liu-head':'https://api.github.com/repos/michaeliu4/frankl-complete-four-sets/commits/HEAD'}.items():
 if name.endswith('head'):get(u,name+'.json');continue
 r={'url':u,'utc':datetime.datetime.now(datetime.timezone.utc).isoformat()}
 try:
  with urllib.request.urlopen(u,timeout=20) as f:b=f.read();r.update(status=f.status,sha256=hashlib.sha256(b).hexdigest());(p/(name+'.pdf')).write_bytes(b)
  import subprocess;subprocess.run(['pdftotext','-layout',str(p/(name+'.pdf')),str(p/(name+'.txt'))])
 except Exception as e:r['error']=str(e)
 out.append(r);(D/'outputs/registry-fetch.json').write_text(json.dumps(out,indent=2))
print(out)
