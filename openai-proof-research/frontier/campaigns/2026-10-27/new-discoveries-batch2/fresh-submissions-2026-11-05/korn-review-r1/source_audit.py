from pathlib import Path
import requests,json,hashlib,datetime,concurrent.futures,re,subprocess
P=Path(__file__).parent; S=P/'receipts';S.mkdir(exist_ok=True)
R=[]
def get(url,name,save=True):
 try:
  r=requests.get(url,timeout=35);b=r.content;d=dict(url=url,status=r.status_code,bytes=len(b),sha256=hashlib.sha256(b).hexdigest(),accessed=datetime.datetime.now(datetime.timezone.utc).isoformat());
  if save:(S/name).write_bytes(b);d['file']='receipts/'+name
  R.append(d);return r
 except Exception as e:R.append(dict(url=url,error=str(e)));return None
for repo,ref in [('openai/math','HEAD'),('the-omega-institute/trureturing','dev')]:
 tag=repo.split('/')[-1];r=get(f'https://api.github.com/repos/{repo}/commits/{ref}',tag+'-head.json');head=r.json()['sha']; print(tag,head,flush=True)
 root=get(f'https://api.github.com/repos/{repo}/git/trees/{head}',tag+'-root.json').json()
 for folder in (['preprints'] if tag=='math' else ['Library','Problems']):
  x=next((x for x in root.get('tree',[]) if x['path']==folder),None)
  if not x:continue
  tree=get(f'https://api.github.com/repos/{repo}/git/trees/{x["sha"]}?recursive=1',tag+'-'+folder+'.json').json(); print(folder,len(tree.get('tree',[])),tree.get('truncated'),flush=True)
  selected=[x for x in tree.get('tree',[]) if x['type']=='blob' and re.search(r'korn|cummings|lorton|elastic|sobolev|trace|helmholtz|boundary|strain|feng',x['path'],re.I) and x['path'].endswith(('.md','.tex','.bib','.txt'))]
  def job(x):
   name=tag+'-'+folder+'-'+hashlib.sha256(x['path'].encode()).hexdigest()[:12]+'.txt'; r=get(f'https://raw.githubusercontent.com/{repo}/{head}/{folder}/{x["path"]}',name);return dict(path=folder+'/'+x['path'],file='receipts/'+name,status=r.status_code if r is not None else None)
  with concurrent.futures.ThreadPoolExecutor(max_workers=6) as ex: bodies=list(ex.map(job,selected))
  (P/(tag+'-'+folder+'-body-index.json')).write_text(json.dumps(bodies,indent=2));print('bodies',len(bodies),flush=True)
for url,name in [('https://arxiv.org/abs/1501.05340','feng-lorton-abs.html'),('https://arxiv.org/pdf/1501.05340','feng-lorton-current.pdf'),('https://www.worldscientific.com/doi/pdf/10.1142/S021820250600108X','cummings-publisher.html'),('https://sites.google.com/utk.edu/xfeng/publications','feng-publications.html'),('https://arxiv.org/abs/1608.07736','geng-abs.html')]:get(url,name)
(P/'source-receipts.json').write_text(json.dumps(R,indent=2))
