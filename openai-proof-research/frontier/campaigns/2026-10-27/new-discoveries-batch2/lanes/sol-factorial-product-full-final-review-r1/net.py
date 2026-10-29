from pathlib import Path
import urllib.request,urllib.error,json,hashlib,datetime,re
L=Path(__file__).resolve().parent; D=L/'network';D.mkdir(exist_ok=True)
repo='the-omega-institute/trureturing'; api='https://api.github.com/repos/'+repo
def get(url,name):
 if (D/name).exists():return (D/name).read_bytes()
 now=datetime.datetime.now(datetime.timezone.utc).isoformat()
 try:
  with urllib.request.urlopen(urllib.request.Request(url,headers={'User-Agent':'Independent-math-review','Accept':'application/vnd.github+json'}),timeout=18) as r:b=r.read(16*1024*1024);status=r.status
 except urllib.error.HTTPError as e:
  with (L/'http.jsonl').open('a') as f:f.write(json.dumps({'utc':now,'url':url,'status':e.code})+'\n')
  raise
 (D/name).write_bytes(b)
 with (L/'http.jsonl').open('a') as f:f.write(json.dumps({'utc':now,'url':url,'status':status,'path':str(D/name),'sha256':hashlib.sha256(b).hexdigest()})+'\n')
 return b
def js(url,name):return json.loads(get(url,name))
out={'base':'0d4df45e499f5e2d97471c506c555c18fd44920c','intervals':[],'bodies':[],'hits':[],'status':'HOLD'}
try:
 head=js(api+'/commits/HEAD','head.json')['sha'];out['head']=head
 out['openai_head']=js('https://api.github.com/repos/openai/math/commits/HEAD','openai-head.json')['sha']
 commits=js(api+'/commits?sha='+head+'&per_page=100','commits.json'); index={c['sha']:c for c in commits}
 chain=[head]
 while chain[-1]!=out['base'] and len(chain)<50:
  c=index.get(chain[-1])
  if c is None:c=js(api+'/commits/'+chain[-1],f'ancestor-{len(chain)}.json')
  chain.append(c['parents'][0]['sha'])
 out['first_parent_chain']=chain
 assert chain[-1]==out['base'],'bounded first-parent chain does not reach base'
 pattern=re.compile(r'factorial|transversal|dissociat|subset.?product|Aivazidis|Loukaki|Gamma.{0,30}/|jgth-2024-0030',re.I)
 seen=set()
 for i,(tip,base) in enumerate(zip(chain,chain[1:])):
  d=js(api+'/compare/'+base+'...'+tip,f'interval-{i}.json')
  assert d['base_commit']['sha']==base and d['merge_base_commit']['sha']==base and d['behind_by']==0
  row={'base':base,'head':tip,'files':len(d['files']),'commits':d['total_commits'],'missing':[]};out['intervals'].append(row)
  if len(d['files'])==300:
   assert d['total_commits']==1,'merge interval capped; no single-commit pagination closure'
   files=[]
   for page in range(1,12):
    c=js(api+'/commits/'+tip+'?per_page=100&page='+str(page),f'commit-files-{i}-{page}.json')
    assert c['parents'][0]['sha']==base
    files.extend(c['files'])
    if len(c['files'])<100:break
   else:raise AssertionError('bounded commit-file pagination exhausted')
   assert len({f['filename'] for f in files})==len(files)
   d['files']=files;row['paginated_files']=len(files)
  for j,f in enumerate(d['files']):
   name=f['filename'];patch=f.get('patch','')
   hit=bool(pattern.search(name+'\n'+patch))
   if hit:out['hits'].append({'interval':i,'path':name,'patch_excerpt':patch[:7000]})
   if (not patch or hit) and f['status']!='removed':
    key=(tip,name)
    if key in seen:continue
    seen.add(key)
    if not patch:row['missing'].append(name)
    b=get('https://raw.githubusercontent.com/'+repo+'/'+tip+'/'+urllib.parse.quote(name),f'body-{i}-{j}.txt')
    txt=b.decode('utf-8',errors='replace');matches=[txt[max(0,m.start()-150):m.end()+350] for m in list(pattern.finditer(txt))[:15]]
    out['bodies'].append({'head':tip,'path':name,'sha256':hashlib.sha256(b).hexdigest(),'matches':matches})
 out['status']='STRUCTURAL_CLOSURE_TARGET_SCREEN_COMPLETE'
except Exception as e:out['error']=repr(e)
(L/'fresh-coverage.json').write_text(json.dumps(out,indent=2)+'\n')
print(json.dumps({k:v for k,v in out.items() if k not in ['hits','bodies','intervals','first_parent_chain']}))
