import pathlib,json,hashlib,re,urllib.request,datetime
L=pathlib.Path(__file__).parent; R=pathlib.Path('/home/mj-kang/Documents/Dev/math/openai-proof-research')
terms=re.compile(r'boxed.mesh|2609.13764|irrational.enumeration|Bevan|Cond[eé]|Heilbronn|Sudermann|critical.triangles|strong.dichotom',re.I)
files=[];hits=[]
for p in R.rglob('*'):
 if not p.is_file() or L in p.parents:continue
 if not (p.name.lower() in ['summary.md','discovery.md','findings.md','proof.md','ledger.json','next.md'] or 'review' in p.name.lower() and p.suffix in ['.md','.json']):continue
 b=p.read_bytes();files.append({'path':str(p.relative_to(R)),'sha256':hashlib.sha256(b).hexdigest()})
 s=b.decode(errors='replace'); lines=[x for x in s.splitlines() if terms.search(x)]
 if lines:hits.append({'path':str(p.relative_to(R)),'lines':lines})
(L/'duplicate-screen.json').write_text(json.dumps({'utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'terms':terms.pattern,'files':files,'hits':hits},indent=2))
print('FILES',len(files),'HITS',len(hits));print(json.dumps(hits,indent=2)[:25000])
urls={'boxed':'https://arxiv.org/html/2609.13764v1','irrational':'https://arxiv.org/html/2412.12972v5','omega-head':'https://api.github.com/repos/the-omega-institute/trureturing/commits/main','openai-head':'https://api.github.com/repos/openai/math/commits/main'}
log=[]
for name,url in urls.items():
 try:
  with urllib.request.urlopen(urllib.request.Request(url,headers={'User-Agent':'research-source-check'}),timeout=25) as r:b=r.read();status=r.status
  (L/'sources'/ (name+'.raw')).write_bytes(b);log.append({'name':name,'url':url,'status':status,'sha256':hashlib.sha256(b).hexdigest(),'bytes':len(b)})
 except Exception as e:log.append({'name':name,'url':url,'error':str(e)})
(L/'http.json').write_text(json.dumps(log,indent=2));print(json.dumps(log,indent=2))
