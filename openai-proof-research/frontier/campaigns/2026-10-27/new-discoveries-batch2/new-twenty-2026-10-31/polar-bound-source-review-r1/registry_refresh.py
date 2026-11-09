from pathlib import Path
import json,urllib.request,urllib.error,hashlib,datetime,resource,os
resource.setrlimit(resource.RLIMIT_CPU,(120,120));resource.setrlimit(resource.RLIMIT_AS,(6*1024**3,6*1024**3));os.sched_setaffinity(0,sorted(os.sched_getaffinity(0))[:2])
o=Path(__file__).resolve().parent;r=o.parent/'expanded-corpus-r255';receipts=[]; blocked=set()
def fetch(name,url):
 host=urllib.request.urlparse(url).netloc if False else url.split('/')[2]
 if host in blocked:return None
 start=datetime.datetime.now(datetime.timezone.utc).isoformat()
 try:
  with urllib.request.urlopen(urllib.request.Request(url,headers={'User-Agent':'independent-source-review'}),timeout=18) as h: body=h.read();status=h.status
 except urllib.error.HTTPError as e:body=e.read();status=e.code
 except Exception as e:body=str(e).encode();status='ERROR'
 if status in (403,429):blocked.add(host)
 (o/(name+'.body')).write_bytes(body);receipts.append(dict(name=name,url=url,utc=start,status=status,sha256=hashlib.sha256(body).hexdigest(),bytes=len(body)));(o/'live-receipts.json').write_text(json.dumps(receipts,indent=2))
 return json.loads(body) if status==200 else None
for name,repo in [('openai','openai/math'),('omega','the-omega-institute/trureturing'),('pool','Vilin97/lean-pool')]:
 h=fetch(name+'-head','https://api.github.com/repos/'+repo+'/commits/HEAD')
 if h:print(name,h['sha'],h['commit']['committer']['date'])
 if name=='pool' and h:
  old=json.loads((r/'pool-tree.body').read_text());print('pool tree',old['truncated'],old['sha'])
  for x in old['tree']:
   p=x['path']
   if x['type']=='blob' and (p=='LeanPool/projects.yml' or p.startswith('candidates/') and p.endswith(('.md','.yml','.jsonl','.txt','.json'))):
    print('INDEX',p)
    # Independently inspect raw current files, not just discovery summaries.
    fetch('pool-raw-'+p.replace('/','-'),'https://raw.githubusercontent.com/'+repo+'/'+h['sha']+'/'+p)
print('DONE')
