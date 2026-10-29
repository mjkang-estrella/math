from pathlib import Path
import urllib.request,json,hashlib,datetime
P=Path(__file__).resolve().parent; out=[]
urls={
'omega-head':'https://api.github.com/repos/the-omega-institute/trureturing/commits/main',
'openai-head':'https://api.github.com/repos/openai/math/commits/main',
'omega-delta':'https://api.github.com/repos/the-omega-institute/trureturing/compare/70af54071bfd4ac098619a9db8c16bb6f7aced11...main',
'openai-delta':'https://api.github.com/repos/openai/math/compare/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a...main',
'lasso-history':'https://arxiv.org/abs/2303.16843',
'comparison-history':'https://arxiv.org/abs/2311.12685',
'henryford-record':'https://scholarlycommons.henryford.com/publichealthsciences_articles/612/'
}
for name,url in urls.items():
 r={'name':name,'url':url,'utc':datetime.datetime.now(datetime.timezone.utc).isoformat()}
 try:
  with urllib.request.urlopen(urllib.request.Request(url,headers={'User-Agent':'research-review/1.0'}),timeout=25) as f:
   b=f.read(20000000); r.update(status=f.status,final_url=f.url,headers=dict(f.headers))
  (P/(name+'.body')).write_bytes(b); r.update(sha256=hashlib.sha256(b).hexdigest(),bytes=len(b))
  if name.endswith('head'):r['head']=json.loads(b)['sha']
  if name.endswith('delta'):
   d=json.loads(b); r.update(total_commits=d.get('total_commits'),files=[x['filename'] for x in d.get('files',[])],commits=[x['sha'] for x in d.get('commits',[])])
 except Exception as e:r['failure']=str(e)
 out.append(r)
(P/'http-provenance.json').write_text(json.dumps(out,indent=2))
print(json.dumps([{k:v for k,v in r.items() if k in ['name','head','failure','total_commits','files']} for r in out],indent=2))
