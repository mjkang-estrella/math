import urllib.request,urllib.error,json,hashlib,datetime,resource,signal,re
from pathlib import Path
resource.setrlimit(resource.RLIMIT_AS,(512*1024**2,)*2);resource.setrlimit(resource.RLIMIT_CPU,(210,210));signal.alarm(220)
D=Path(__file__).resolve().parent;(D/'live').mkdir(exist_ok=True);rows=[]
def get(name,url):
 row=dict(url=url,started_utc=datetime.datetime.now(datetime.timezone.utc).isoformat());b=None
 try:
  with urllib.request.urlopen(urllib.request.Request(url,headers={'User-Agent':'source-prior-review/1.0','Accept':'application/vnd.github+json'}),timeout=15) as f:
   b=f.read(16*1024**2+1);row.update(status=f.status,final_url=f.url)
   if len(b)>16*1024**2:raise ValueError('body cap; not complete')
  (D/'live'/name).write_bytes(b);row.update(bytes=len(b),sha256=hashlib.sha256(b).hexdigest(),file='live/'+name)
 except Exception as e:row['error']=str(e);b=None
 row['finished_utc']=datetime.datetime.now(datetime.timezone.utc).isoformat();rows.append(row);(D/'http.json').write_text(json.dumps(rows,indent=2));return json.loads(b) if b else None
repos={'omega':'the-omega-institute/trureturing','openai':'openai/math','aim':'MColbrook/AIM','count':'suvrit/count-ex-machina'}
heads={}
for name,repo in repos.items():
 api='https://api.github.com/repos/'+repo+'/'
 b=get(name+'-head.json',api+'commits/'+('dev' if name=='omega' else 'HEAD'))
 if not b:continue
 head=b['sha'];heads[name]=dict(head=head,date=b['commit']['committer']['date'],message=b['commit']['message'])
 if name=='omega':
  main=get('omega-main.json',api+'commits/main')
  if main:heads['omega-main']=dict(head=main['sha'],date=main['commit']['committer']['date'])
 root=get(name+'-root.json',api+'git/trees/'+head)
 if root:
  targets={'omega':['D5','Problems'],'openai':['preprints'],'aim':['AIM'],'count':[]}[name]
  # AIM root actual names recorded; full root recursive if target absent.
  selected=[x for x in root.get('tree',[]) if x['path'] in targets and x['type']=='tree']
  if selected:
   for x in selected:get(name+'-'+x['path']+'.json',api+'git/trees/'+x['sha']+'?recursive=1')
  else:get(name+'-complete.json',api+'git/trees/'+head+'?recursive=1')
(D/'heads.json').write_text(json.dumps(heads,indent=2));print(json.dumps(heads,indent=2))
