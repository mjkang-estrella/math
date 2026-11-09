from pathlib import Path
import urllib.request,urllib.error,json,hashlib,datetime,sys
L=Path(__file__).resolve().parent; (L/'receipts').mkdir(exist_ok=True)
def fetch(name,url):
 p=L/'receipts'/name
 if p.exists(): return p.read_bytes()
 r={'url':url,'utc':datetime.datetime.now(datetime.timezone.utc).isoformat()}
 try:
  with urllib.request.urlopen(urllib.request.Request(url,headers={'User-Agent':'independent-mathematics-review'}),timeout=35) as f: b=f.read();r.update(status=f.status,final_url=f.url)
 except urllib.error.HTTPError as e: b=e.read();r.update(status=e.code,error=str(e))
 except Exception as e: b=b'';r.update(status=None,error=str(e))
 p.write_bytes(b);r.update(bytes=len(b),sha256=hashlib.sha256(b).hexdigest());p.with_suffix(p.suffix+'.receipt.json').write_text(json.dumps(r,indent=2));print(name,r.get('status'),len(b),flush=True);return b
if __name__=='__main__':
 for repo,tag in [('openai/math','openai'),('the-omega-institute/trureturing','omega'),('Vilin97/lean-pool','pool')]:
  h=json.loads(fetch(tag+'-head.json','https://api.github.com/repos/'+repo+'/commits/HEAD'));sha=h['sha']
  t=json.loads(fetch(tag+'-tree.json','https://api.github.com/repos/'+repo+'/git/trees/'+sha+'?recursive=1'))
  # Traverse each immediate subtree in a truncated root, never pretend truncation is clearance.
  if t.get('truncated'):
   root=json.loads(fetch(tag+'-root.json','https://api.github.com/repos/'+repo+'/git/trees/'+sha));paths=[]
   for e in root['tree']:
    if e['type']=='tree':
     sub=json.loads(fetch(tag+'-sub-'+e['path'].replace('/','_')+'.json','https://api.github.com/repos/'+repo+'/git/trees/'+e['sha']+'?recursive=1'))
     paths += [dict(x,path=e['path']+'/'+x['path']) for x in sub.get('tree',[])];print('SUBTREE',tag,e['path'],sub.get('truncated'),flush=True)
    else:paths.append(e)
  else: paths=t.get('tree',[])
  (L/(tag+'-paths.json')).write_text(json.dumps(paths))
  for e in paths:
   p=e['path']; low=p.lower()
   if e['type']=='blob' and ((tag=='pool' and (p.startswith('candidates/') or p=='LeanPool/projects.yml')) or any(w in low for w in ['matroid','lason','lasoń','332371']) or (tag=='openai' and p=='overview.tex')):
    fetch(tag+'--'+p.replace('/','__'),'https://raw.githubusercontent.com/'+repo+'/'+sha+'/'+p)
 fetch('workshop.pdf','https://orderandgeometry2016.tcs.uj.edu.pl/docs/OG2016-Problem-Booklet.pdf')
