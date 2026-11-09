import pathlib,urllib.request,json,hashlib,datetime,re
L=pathlib.Path(__file__).resolve().parents[1];rec=[]
base='https://api.github.com/repos/openai/math/git/trees/'
def get(name,url):
 with urllib.request.urlopen(urllib.request.Request(url,headers={'User-Agent':'Research evidence'}),timeout=20) as s:d=s.read();status=s.status
 (L/'sources'/name).write_bytes(d)
 rec.append(dict(file=name,url=url,status=status,sha256=hashlib.sha256(d).hexdigest(),utc=datetime.datetime.now(datetime.timezone.utc).isoformat()))
 (L/'outputs/openai-scope-receipts.json').write_text(json.dumps(rec,indent=2))
 return json.loads(d)
try:
 root=get('openai-root.json',base+'4eaee87548250b2682affda7d05d947c05554bae')
 x=next(x for x in root['tree'] if x['path']=='preprints')
 t=get('openai-preprints.json',base+x['sha']+'?recursive=1')
 print('preprints truncated',t.get('truncated'),'entries',len(t['tree']))
 for x in t['tree']:
  if re.search('word.?represent|toroidal.?grid|cylindric|representation.number',x['path'],re.I):print(x)
except Exception as e:print('failure',repr(e))
