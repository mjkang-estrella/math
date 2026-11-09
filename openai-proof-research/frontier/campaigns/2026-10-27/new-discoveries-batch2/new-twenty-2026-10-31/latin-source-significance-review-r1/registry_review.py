import pathlib,json,urllib.request,hashlib,datetime,resource,re
resource.setrlimit(resource.RLIMIT_AS,(1024**3,1024**3));resource.setrlimit(resource.RLIMIT_CPU,(50,50))
r=pathlib.Path(__file__).parent; receipts=[]
def get(name,url):
 d={'name':name,'url':url,'utc':datetime.datetime.now(datetime.timezone.utc).isoformat()}
 try:
  with urllib.request.urlopen(url,timeout=20) as f:
   b=f.read();(r/name).write_bytes(b);d.update(status=f.status,sha256=hashlib.sha256(b).hexdigest(),bytes=len(b));out=b
 except Exception as e:d.update(error=str(e));out=b'{}'
 receipts.append(d);(r/'registry-receipts.json').write_text(json.dumps(receipts,indent=2));print(d,flush=True);return json.loads(out) if name.endswith('.json') else out
head=json.loads((r/'omega-head.json').read_text())['sha']; root=get('omega-root.json',f'https://api.github.com/repos/the-omega-institute/trureturing/git/trees/{head}')
pat=re.compile('haystack|locker|czumaj|kontogeorg|paterson|latin|permutation|guess|cover',re.I)
matches=[]
for e in root.get('tree',[]):
 if e['type']=='tree' and e['path'] in ['Library','Problems']:
  t=get('omega-'+e['path']+'.json',f'https://api.github.com/repos/the-omega-institute/trureturing/git/trees/{e["sha"]}?recursive=1')
  for x in t.get('tree',[]):
   if x['type']=='blob' and pat.search(x['path']):matches.append(dict(x,fullpath=e['path']+'/'+x['path']))
(r/'registry-matches.json').write_text(json.dumps(matches,indent=2));print('MATCHES',[(x['fullpath'],x['sha']) for x in matches],flush=True)
# Read all bounded relevant filename matches, no clearance inferred from missing names.
for j,x in enumerate(matches):
 get(f'omega-body-{j}.txt',f'https://raw.githubusercontent.com/the-omega-institute/trureturing/{head}/{x["fullpath"]}')
get('covering.pdf','https://arxiv.org/pdf/1811.09040')
