from pathlib import Path
import urllib.request,hashlib,json,datetime
D=Path.cwd()/'receipts'
def get(n,url):
 p=D/(n+'.body')
 if p.exists():return p.read_bytes()
 r=dict(url=url,utc=datetime.datetime.now(datetime.timezone.utc).isoformat());data=None
 try:
  with urllib.request.urlopen(urllib.request.Request(url,headers={'User-Agent':'independent-math-review'}),timeout=20) as f:data=f.read();r.update(status=f.status,final_url=f.url)
  p.write_bytes(data);r['sha256']=hashlib.sha256(data).hexdigest()
 except Exception as e:r['error']=str(e)
 (D/(n+'.json')).write_text(json.dumps(r,indent=2));print(r,flush=True)
 return data
for short,repo in [('openai','openai/math'),('omega','the-omega-institute/trureturing'),('authors','Shivaramkratos/Ultimate_Independence_ratio_Python_Gurobi_code')]:
 h=json.loads((D/(short+'-head.body')).read_bytes());sha=h['sha'];base='https://api.github.com/repos/'+repo
 root=json.loads(get(short+'-root',base+'/git/trees/'+h['commit']['tree']['sha']))
 if short=='authors':
  for e in root['tree']:
   if e['type']=='blob':get('authors-'+e['path'].replace('/','_'),'https://raw.githubusercontent.com/'+repo+'/'+sha+'/'+e['path'])
 else:
  for e in root['tree']:
   if e['path'] in ['preprints','D5','Problems']:
    data=get(short+'-'+e['path'],base+'/git/trees/'+e['sha']+'?recursive=1')
    if not data:continue
    tree=json.loads(data);hits=[x for x in tree.get('tree',[]) if any(k in x['path'].lower() for k in ['wheel','fractionalchrom','fractional_chrom','2511.18747'])]
    (D/(short+'-'+e['path']+'-hits.json')).write_text(json.dumps(dict(entries=len(tree.get('tree',[])),truncated=tree.get('truncated'),hits=hits),indent=2))
    for x in hits:
     if x['type']=='blob':get(short+'-hit-'+x['sha'],'https://raw.githubusercontent.com/'+repo+'/'+sha+'/'+e['path']+'/'+x['path'])
