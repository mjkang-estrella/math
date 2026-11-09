from pathlib import Path
import urllib.request,json,datetime,hashlib
B=Path(__file__).resolve().parent
records=[]
def get(name,url):
 r={'url':url,'utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'file':name}
 try:
  with urllib.request.urlopen(urllib.request.Request(url,headers={'User-Agent':'Public mathematical research'}),timeout=30) as f:d=f.read();r['status']=f.status
  (B/'sources'/name).write_bytes(d);r['sha256']=hashlib.sha256(d).hexdigest();r['bytes']=len(d)
  return json.loads(d) if name.endswith('.json') else d
 except Exception as e:r['error']=str(e)
 finally:records.append(r);(B/'retrieval.json').write_text(json.dumps(records,indent=2))
if __name__=='__main__':
 h=json.loads((B/'sources/omega-head.json').read_text())['sha']
 root=get('omega-root.json',f'https://api.github.com/repos/the-omega-institute/trureturing/git/trees/{h}')
 for p in ['Problems','D5','Blueprint']:
  e=next(x for x in root['tree'] if x['path']==p)
  d=get('omega-'+p+'-tree.json',f'https://api.github.com/repos/the-omega-institute/trureturing/git/trees/{e["sha"]}?recursive=1')
  assert d and not d['truncated']
  old=json.loads((B.parent/'root-percolation-poisson-r1'/'sources'/('omega-'+p+'-tree.json')).read_text())
  old={x['path']:x['sha'] for x in old['tree']}
  changes=[x for x in d['tree'] if x['type']=='blob' and old.get(x['path'])!=x['sha']]
  print(p,len(d['tree']),'changed',len(changes),[x['path'] for x in changes])
  for i,e in enumerate(changes):
   get(f'omega-change-{p}-{i}.txt',f'https://raw.githubusercontent.com/the-omega-institute/trureturing/{h}/{p}/{e["path"]}')
 get('vandenberg1996.pdf','https://ir.cwi.nl/pub/2208/2208D.pdf')
