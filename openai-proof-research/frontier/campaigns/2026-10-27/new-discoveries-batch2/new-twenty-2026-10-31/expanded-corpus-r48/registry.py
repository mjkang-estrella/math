exec(open(__file__.replace('registry.py','fetch.py')).read().split('urls=')[0])
receipts=[]
def get(name,url):
 r=requests.get(url,timeout=20);f=p/'sources'/(name+'.json');f.write_bytes(r.content);receipts.append({'utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'url':url,'status':r.status_code,'file':str(f),'sha256':hashlib.sha256(r.content).hexdigest()});(p/'registry-receipts.json').write_text(json.dumps(receipts,indent=2)+'\n');r.raise_for_status();return r.json()
h=json.loads((p/'sources/omega-head.json').read_text());root=get('omega-root','https://api.github.com/repos/the-omega-institute/trureturing/git/trees/'+h['commit']['tree']['sha']);hits=[]
for name in ['D5','Problems']:
 node=next(x for x in root['tree'] if x['path']==name);d=get('omega-'+name,node['url']+'?recursive=1');assert not d.get('truncated');hits.extend({'section':name,**x} for x in d['tree'] if any(s in x['path'].lower() for s in ['staller','makerbreaker','maker-breaker','bujtas','crossframe','nonnegativetensor','primefold','extremetensor']))
(p/'omega-hits.json').write_text(json.dumps(hits,indent=2)+'\n');print(json.dumps(hits,indent=2))
