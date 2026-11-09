import pathlib,urllib.request,json,hashlib,datetime,re
p=pathlib.Path.cwd();log=[]
def get(k,u):
 try:
  with urllib.request.urlopen(u,timeout=20) as f:b=f.read()
  (p/'sources'/f'{k}.json').write_bytes(b);log.append({'key':k,'url':u,'utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'status':200,'sha256':hashlib.sha256(b).hexdigest()});return json.loads(b)
 except Exception as e:log.append({'key':k,'url':u,'error':str(e)});return {}
sha=json.loads((p/'sources/omega-head.html').read_text())['sha'];root=get('omega-root','https://api.github.com/repos/the-omega-institute/trureturing/git/trees/'+sha)
for obj in root.get('tree',[]):
 if obj['path'] in ['D5','Problems']:
  d=get('omega-'+obj['path'],'https://api.github.com/repos/the-omega-institute/trureturing/git/trees/'+obj['sha']+'?recursive=1')
  paths=[o['path'] for o in d.get('tree',[])];hits=[s for s in paths if re.search('12770|SplitGraph|HamiltonConnect|MinimalCodeword|MaximumWeighted|Cichacz|Detachable|Hippchen',s,re.I)]
  print(obj['path'],'truncated=',d.get('truncated'),'entries=',len(paths),'hits=',hits)
(p/'outputs/registry-receipts.json').write_text(json.dumps(log,indent=2))
