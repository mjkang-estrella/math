from pathlib import Path
import urllib.request,json,hashlib,datetime,subprocess
D=Path(__file__).parent; (D/'live').mkdir(exist_ok=True); rows=[]
def get(url,name):
 row={'url':url,'utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'path':'live/'+name};value=None
 try:
  with urllib.request.urlopen(urllib.request.Request(url,headers={'User-Agent':'mathematical-source-review'}),timeout=22) as r:
   data=r.read(18000000);row.update(status=r.status,bytes=len(data),sha256=hashlib.sha256(data).hexdigest(),final_url=r.url);(D/row['path']).write_bytes(data)
   if name.endswith('.json'):value=json.loads(data)
   if data.startswith(b'%PDF'):subprocess.run(['pdftotext','-layout',str(D/row['path']),str(D/row['path'])+'.txt'],check=True)
 except Exception as e:row['error']=str(e)
 rows.append(row);(D/'http-receipts.json').write_text(json.dumps(rows,indent=2));return value
for name,repo,old in [('omega','the-omega-institute/trureturing','9aef67a59dec08d1ff04a18a3d23560525ab023d'),('openai','openai/math','7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a')]:
 h=get('https://api.github.com/repos/'+repo+'/commits/HEAD',name+'-head.json')
 if h and h['sha']!=old:get('https://api.github.com/repos/'+repo+'/compare/'+old+'...'+h['sha'],name+'-delta.json')
get('https://mirkogiacchini.github.io/publications.html','author-publications.html')
get('https://mirkogiacchini.github.io/papers/cgk25_chatterjee_metricity.pdf','author-accepted.pdf')
get('https://api.github.com/repos/mirkogiacchini/metricityChatterjeeCoefficient/git/trees/HEAD?recursive=1','author-code-tree.json')
get('https://arxiv.org/pdf/2505.08045','rockel.pdf')
get('https://arxiv.org/pdf/1204.0405','ruankong.pdf')
get('https://arxiv.org/pdf/2606.07354','adapted.pdf')
print(json.dumps(rows,indent=2))
