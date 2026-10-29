from pathlib import Path
import urllib.request,json,hashlib,datetime,concurrent.futures
out=Path('evidence');out.mkdir(exist_ok=True); records=[]
def get(n,u):
 try:
  with urllib.request.urlopen(urllib.request.Request(u,headers={'User-Agent':'research-read-only-review'}),timeout=45) as r:d=r.read();status=r.status
  (out/n).write_bytes(d);records.append(dict(name=n,url=u,status=status,utc=datetime.datetime.now(datetime.timezone.utc).isoformat(),sha256=hashlib.sha256(d).hexdigest(),bytes=len(d)));return json.loads(d) if n.endswith('.json') else d
 except Exception as e:records.append(dict(name=n,url=u,error=str(e)));return None
with concurrent.futures.ThreadPoolExecutor(6) as ex:
 jobs=[ex.submit(get,n,u) for n,u in [('primary.html','https://arxiv.org/html/2608.23006v2'),('companion.html','https://arxiv.org/html/2609.29531v2'),('primary-abs.html','https://arxiv.org/abs/2608.23006'),('companion-abs.html','https://arxiv.org/abs/2609.29531')]]
 for j in jobs:j.result()
for label,repo,dirs in [('openai','openai/math',['preprints']),('omega','the-omega-institute/trureturing',['Problems','D5','Blueprint'])]:
 h=get(label+'-head.json',f'https://api.github.com/repos/{repo}/commits/HEAD')
 if not h:continue
 print(label,h['sha'],h['commit']['committer']['date'],flush=True)
 root=get(label+'-root.json',f'https://api.github.com/repos/{repo}/git/trees/{h["sha"]}')
 for dn in dirs:
  ent=next(x for x in root['tree'] if x['path']==dn);tree=get(label+'-'+dn+'-tree.json',f'https://api.github.com/repos/{repo}/git/trees/{ent["sha"]}?recursive=1');assert tree and not tree['truncated'];print(dn,len(tree['tree']),flush=True)
 get(label+'-readme.md',f'https://raw.githubusercontent.com/{repo}/{h["sha"]}/'+('CONTENTS.md' if label=='openai' else 'README.md'))
(out/'retrieval.json').write_text(json.dumps(records,indent=2))
