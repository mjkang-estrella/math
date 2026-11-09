import urllib.request,json,hashlib,datetime,resource,re,subprocess
from pathlib import Path
resource.setrlimit(resource.RLIMIT_CPU,(40,40));resource.setrlimit(resource.RLIMIT_AS,(768*1024**2,)*2)
r=Path(__file__).parent; a=r.parent/'expanded-corpus-r48';receipts=[]
def get(name,url):
 with urllib.request.urlopen(url,timeout=25) as q:data=q.read(25*1024**2);status=q.status;final=q.url
 (r/name).write_bytes(data);receipts.append({'url':url,'status':status,'final_url':final,'file':name,'bytes':len(data),'sha256':hashlib.sha256(data).hexdigest(),'utc':datetime.datetime.now(datetime.timezone.utc).isoformat()});(r/'additional-http.json').write_text(json.dumps(receipts,indent=2));return data
for name,id in [('original-correct','1807.09479'),('partition','2406.15165'),('minimum','2606.04824'),('complexity','2601.08562')]:
 get(name+'.pdf','https://arxiv.org/pdf/'+id);subprocess.run(['pdftotext','-layout',str(r/(name+'.pdf')),str(r/(name+'.txt'))],check=True)
h=json.loads((r/'omega-head.json').read_text());root=json.loads(get('omega-root.json','https://api.github.com/repos/the-omega-institute/trureturing/git/trees/'+h['commit']['tree']['sha']));hits=[];changes={}
for name in ['D5','Problems']:
 node=next(x for x in root['tree'] if x['path']==name);d=json.loads(get('omega-'+name+'.json',node['url']+'?recursive=1'));assert not d.get('truncated');old=json.loads((a/'sources'/('omega-'+name+'.json')).read_text());od={x['path']:x.get('sha') for x in old['tree']};nd={x['path']:x.get('sha') for x in d['tree']};changes[name]=[p for p in sorted(od.keys()|nd.keys()) if od.get(p)!=nd.get(p)]
 for x in d['tree']:
  if re.search('game|staller|domination|maker.?breaker|355140|bujt|SMB',x['path'],re.I):hits.append({'section':name,**x})
(r/'registry-changes-hits.json').write_text(json.dumps({'head':h['sha'],'changes':changes,'hits':hits},indent=2));print('changes',changes);print('hits',[(x['section'],x['path']) for x in hits])
