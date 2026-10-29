import resource,signal,os,json,urllib.request,datetime,re,hashlib
resource.setrlimit(resource.RLIMIT_AS,(536870912,536870912));resource.setrlimit(resource.RLIMIT_CPU,(20,20));signal.alarm(55)
from pathlib import Path
p=Path('frozen-copy/sources'); out={'utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'inventories':{},'live':[]}
for n in ['omega-D5.json','omega-Problems.json','omega-main-full.json','omega-dev-full.json','inherited-openai-openai-preprints-tree.json','inherited-aim-full-current-tree.json','inherited-count-count-full-tree.json']:
 d=json.loads((p/n).read_bytes()); paths=[x['path'] for x in d['tree']]; hits=[x for x in paths if re.search(r'hankel|sakaguchi|lupa[sşș]|tayyah|sok[oó][lł]|symmetric.?domain|1307|1244',x,re.I)];out['inventories'][n]={'sha':d['sha'],'entries':len(paths),'truncated':d.get('truncated'),'hits':hits}
urls=[('omega-dev','https://api.github.com/repos/the-omega-institute/trureturing/git/trees/dev'),('omega-main','https://api.github.com/repos/the-omega-institute/trureturing/commits/main'),('openai','https://api.github.com/repos/openai/math/commits/main'),('aim','https://api.github.com/repos/MColbrook/AIM/commits/main'),('count','https://api.github.com/repos/suvrit/count-ex-machina/commits/main')]
for name,url in urls:
 rec={'name':name,'url':url,'utc':datetime.datetime.now(datetime.timezone.utc).isoformat()}
 try:
  with urllib.request.urlopen(urllib.request.Request(url,headers={'User-Agent':'independent-math-review'}),timeout=7) as r: data=r.read();rec['status']=r.status
  Path('live-'+name+'.json').write_bytes(data); d=json.loads(data);rec.update(sha=d.get('sha'),date=d.get('commit',{}).get('committer',{}).get('date'),sha256=hashlib.sha256(data).hexdigest())
  if name=='omega-dev': rec['scoped_trees']=[x for x in d['tree'] if x['path'] in ['D5','Problems']]
 except Exception as e:rec['error']=str(e)
 out['live'].append(rec)
Path('registry-evidence.json').write_text(json.dumps(out,indent=2));print(json.dumps(out,indent=2))
