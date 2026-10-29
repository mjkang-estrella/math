from pathlib import Path
import urllib.request,json,datetime,subprocess
P=Path(__file__).parent; log=[]
urls={}
for id in ['2603.24017','2607.08869','2606.01771']:
 urls[id+'-abs.html']='https://arxiv.org/abs/'+id
for id,v in [('2603.24017','2'),('2607.08869','1'),('2606.01771','4')]:
 urls[id+'.pdf']='https://arxiv.org/pdf/'+id+'v'+v
 urls[id+'.html']='https://arxiv.org/html/'+id+'v'+v
for repo in ['the-omega-institute/trureturing','openai/math']:
 urls[repo.split('/')[0]+'-HEAD.json']='https://api.github.com/repos/'+repo+'/commits/HEAD'
for name,url in urls.items():
 try:
  with urllib.request.urlopen(urllib.request.Request(url,headers={'User-Agent':'research-source-audit'}),timeout=35) as r:
   b=r.read(12000000); (P/'sources'/name).write_bytes(b); log.append({'url':url,'file':name,'status':r.status,'utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'bytes':len(b)})
  if name.endswith('.pdf'): subprocess.run(['pdftotext','-layout',str(P/'sources'/name),str(P/'sources'/(name+'.txt'))],check=True)
 except Exception as e:log.append({'url':url,'error':str(e)})
(P/'fetch-log.json').write_text(json.dumps(log,indent=2)); print(json.dumps(log,indent=2))
