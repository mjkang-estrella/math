from pathlib import Path
import json,urllib.request,urllib.error,hashlib,datetime,sys,re,subprocess
L=Path(__file__).resolve().parent;B=L.parent
R=L/'retrieved';R.mkdir(exist_ok=True)
def fetch(url,name):
 p=R/name
 if p.exists():return p.read_bytes()
 rec={'utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'url':url,'file':str(p.relative_to(L))}
 try:
  with urllib.request.urlopen(urllib.request.Request(url,headers={'User-Agent':'bounded-math-source-review'}),timeout=25) as f: data=f.read(60000000);rec.update(status=f.status,final_url=f.url)
  p.parent.mkdir(parents=True,exist_ok=True);p.write_bytes(data);rec.update(bytes=len(data),sha256=hashlib.sha256(data).hexdigest())
 except Exception as e:rec['error']=str(e);data=None
 with (L/'http.jsonl').open('a') as f:f.write(json.dumps(rec)+'\n')
 return data
def api(s):
 d=fetch('https://api.github.com/repos/the-omega-institute/trureturing/'+s,'api/'+hashlib.sha256(s.encode()).hexdigest()+'.json')
 if d is None:raise RuntimeError(s)
 try:return json.loads(d)
 except json.JSONDecodeError:
  p=R/('api/'+hashlib.sha256(s.encode()).hexdigest()+'.json');p.rename(p.with_suffix('.partial'));return api(s)
if __name__=='__main__':
 mode=sys.argv[1]
 if mode=='compare':
  pts=['aa026efa802f4361758b827d6b68231ac353948f','a19a578cd06b57a4ea4d287cb0df92f9085117ae','490f6bccbf445ab8e111a16b0b8670a5dd7c9a9c']
  rows=[]
  for a,b in zip(pts,pts[1:]):
   pages=[];commits=[];page=1
   while True:
    d=api(f'compare/{a}...{b}?per_page=100&page={page}');pages.append(d);commits+=d['commits']
    if len(commits)>=d['total_commits']:break
    assert d['commits'];page+=1
   rows.append({'base':a,'head':b,'total':d['total_commits'],'commits':[{'sha':x['sha'],'parents':[p['sha'] for p in x['parents']],'tree':x['commit']['tree']['sha'],'message':x['commit']['message']} for x in commits]})
  (L/'interval-commits.json').write_text(json.dumps(rows,indent=2));print([(x['total'],x['base'],x['head']) for x in rows])
 elif mode=='trees':
  rows=json.loads((L/'interval-commits.json').read_text());changes=[]
  def tree(s):
   from local_objects import local_tree
   local=local_tree(s)
   if local is not None:
    p=R/('local-trees/'+s+'.json');p.parent.mkdir(exist_ok=True)
    if not p.exists():p.write_text(json.dumps({'sha':s,'tree':list(local.values()),'truncated':False,'route':'read-only libgit2 tree lookup; no git executable or repository writes'}))
    return local
   d=api('git/trees/'+s);assert not d.get('truncated');return {x['path']:x for x in d['tree']}
  def walk(a,b,prefix=''):
   if a==b:return []
   aa=tree(a) if a else {};bb=tree(b) if b else {};out=[]
   for p in sorted(aa.keys()|bb.keys()):
    x=aa.get(p);y=bb.get(p)
    if x and y and x['sha']==y['sha']:continue
    if (x or y)['type']=='tree':out+=walk(x['sha'] if x else None,y['sha'] if y else None,prefix+p+'/')
    else:out.append({'path':prefix+p,'old':x['sha'] if x else None,'new':y['sha'] if y else None})
   return out
  for row in rows:
   for c in row['commits']:
    for parent in c['parents']:
     name=f"changes/{parent}-{c['sha']}.json";q=R/name
     if q.exists():v=json.loads(q.read_text())
     else:
      par=api('git/commits/'+parent);v=walk(par['tree']['sha'],c['tree']);q.parent.mkdir(exist_ok=True);q.write_text(json.dumps(v))
     changes.append({'parent':parent,'commit':c['sha'],'changes_file':str(q.relative_to(L)),'count':len(v)})
     (L/'change-index.json').write_text(json.dumps(changes,indent=2));print(c['sha'],len(v),flush=True)
 elif mode=='citations':
  ds=json.loads((L/'citation-abstracts.json').read_text())
  for i,x in enumerate(ds):
   if i in [3,6]:continue
   ar=next((p for u,p in x['locations'] if p and 'arxiv.org/pdf/' in p),None)
   if ar:
    d=fetch(ar,f'citations/{i+1}.pdf')
    if d and d.startswith(b'%PDF'):subprocess.run(['pdftotext','-layout',str(R/f'citations/{i+1}.pdf'),str(R/f'citations/{i+1}.txt')],check=True)
   elif not x['abstract']:
    fetch(x['doi'],f'citations/{i+1}.html')
  print('citation fetch done')
