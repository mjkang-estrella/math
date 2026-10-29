import datetime,hashlib,json,re,subprocess,gzip
from pathlib import Path
P=Path(__file__).resolve().parent;old=P.parent/'root-edge-irregulator-current-prior-r1'
def sha(p):
 h=hashlib.sha256()
 with p.open('rb') as f:
  for c in iter(lambda:f.read(1048576),b''):h.update(c)
 return h.hexdigest()
base=['git','-c','pack.threads=1','-c','index.threads=1','-c','core.packedGitWindowSize=16m','-c','core.packedGitLimit=64m']
results={}
for repo,url in [('omega','https://github.com/the-omega-institute/trureturing.git'),('openai','https://github.com/openai/math.git')]:
 g=base+['--git-dir='+str(old/(repo+'.git'))]
 head=subprocess.check_output(base+['ls-remote',url,'HEAD'],text=True).split()[0]
 subprocess.run(g+['fetch','--depth=1','--filter=blob:none','origin',head],check=True)
 tree=P/(repo+'-tree.txt')
 with tree.open('w') as f:subprocess.run(g+['ls-tree','-r',head],stdout=f,check=True)
 oldhead=json.loads((old/'CURRENT-REGISTRIES.json').read_text())[repo]['head']
 delta=subprocess.check_output(g+['diff','--name-status',oldhead,head],text=True)
 (P/(repo+'-delta.txt')).write_text(delta)
 matches=[];count=0
 with tree.open() as f:
  for line in f:
   count+=1;path=line.rstrip('\n').split('\t',1)[1]
   if re.search(r'irregular|irregulator|bensmail|catherinot|fioravantes|marcille|oijid|2511[.-]14514',path,re.I):matches.append(path)
 for path in matches:
  if repo=='omega' and path.startswith(('Problems/','D5/')):
   dest=P/'current-bodies'/path;dest.parent.mkdir(parents=True,exist_ok=True)
   with dest.open('wb') as f:subprocess.run(g+['show',head+':'+path],stdout=f,check=True)
 if repo=='openai':
  with (P/'openai-CONTENTS.md').open('wb') as f:subprocess.run(g+['show',head+':CONTENTS.md'],stdout=f,check=True)
 with tree.open('rb') as f,(P/(repo+'-tree.txt.gz')).open('wb') as out:
  with gzip.GzipFile(filename='',mode='wb',fileobj=out,mtime=0) as z:
   for c in iter(lambda:f.read(1048576),b''):z.write(c)
 results[repo]={'head':head,'old_head':oldhead,'entries':count,'complete_recursive_tree':True,'tree_sha256':sha(tree),'delta_lines':len(delta.splitlines()),'target_matches':matches}
results['utc']=datetime.datetime.now(datetime.timezone.utc).isoformat()
results['route']='Ordinary public Git smart HTTP, same repositories, no credentials/API retry/proxy; root-only cache fetch. Existing snapshots left unchanged.'
results['limits']='Complete tree and old-to-new changed path inventory, selected matching bodies; not a semantic audit of every file or worldwide priority.'
(P/'CURRENT-REGISTRIES.json').write_text(json.dumps(results,indent=2)+'\n')
print(json.dumps(results,indent=2))
