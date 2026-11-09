import pathlib,json,urllib.request,hashlib,datetime
D=pathlib.Path(__file__).resolve().parents[1]
def get(key,url):
 rec={'url':url,'utc':datetime.datetime.now(datetime.timezone.utc).isoformat()}
 try:
  with urllib.request.urlopen(url,timeout=12) as r:b=r.read();rec.update(status=r.status,sha256=hashlib.sha256(b).hexdigest(),bytes=len(b));(D/'sources'/key).write_bytes(b)
  obj=json.loads(b)
 except Exception as e:rec['error']=str(e);obj={}
 (D/'sources'/(key+'.receipt.json')).write_text(json.dumps(rec,indent=2)+'\n');return obj
h=json.loads((D/'sources/omega-head.json').read_text())['sha'];root=get('omega-root.json',f'https://api.github.com/repos/the-omega-institute/trureturing/git/trees/{h}')
for row in root.get('tree',[]):
 if row['path'] in ['D5','Problems']:
  get('omega-'+row['path']+'.json',row['url']+'?recursive=1')
h=json.loads((D/'sources/openai-head.json').read_text())['sha'];root=get('openai-root.json',f'https://api.github.com/repos/openai/math/git/trees/{h}')
for row in root.get('tree',[]):
 if row['path']=='preprints':get('openai-preprints.json',row['url']+'?recursive=1')
patterns=['sylvester','signedshift','signed-shift','burning','puleo','sequential','additivecolor','additive-color','signature','manickam','stein','wythoff','lubell','pancyclic','clique-decomposition','recolor']
res={}
for p in (D/'sources').glob('*-*.json'):
 if p.name.endswith('receipt.json'):continue
 try:o=json.loads(p.read_text())
 except:continue
 if 'tree' not in o:continue
 res[p.name]={'truncated':o.get('truncated'),'count':len(o['tree']),'matches':[r for r in o['tree'] if any(s in r['path'].lower() for s in patterns)]}
(D/'outputs/registry-screen.json').write_text(json.dumps(res,indent=2)+'\n');print({k:(v['truncated'],v['count'],len(v['matches'])) for k,v in res.items()})
