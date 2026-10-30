import pathlib,json,hashlib,urllib.request,datetime,re,shutil
from audit import B,L,sha
R=L/'research';R.mkdir(exist_ok=True)
log=[]
def get(name,url):
 try:
  with urllib.request.urlopen(urllib.request.Request(url,headers={'User-Agent':'research-source-review/1.0'}),timeout=25) as h:
   b=h.read(12*1024*1024);p=R/name;p.write_bytes(b);log.append(dict(name=name,url=url,final_url=h.url,status=h.status,bytes=len(b),sha256=sha(p),utc=datetime.datetime.now(datetime.timezone.utc).isoformat()));return b
 except Exception as e:log.append(dict(name=name,url=url,error=str(e),utc=datetime.datetime.now(datetime.timezone.utc).isoformat()));return None
S=B/'lanes/sol-steiner-gp-source-prior-review-r2'
inputs={'blueprint':S/'retrieved/omega-blueprint-tree.json','problems':S/'copies/root-r165-preliminary-freeze-r1/sol-fresh-source-discovery-r165/sources/omega-current-problems.json','omega-root':S/'retrieved/omega-root.json','delta':S/'retrieved/omega-fixed-delta.json'}
for n,p in inputs.items():shutil.copyfile(p,R/(n+'.json'))
O='2b143c68ca72fcaccfe71d6233cb2c6db4c8c059';A='4eaee87548250b2682affda7d05d947c05554bae'
get('openai-tree.json',f'https://api.github.com/repos/openai/math/git/trees/{A}?recursive=1')
get('current-citers.json','https://api.openalex.org/works?filter=cites:W3097405001&per-page=20')
aliases=['1907.13009','s13370-020-00851-9','Steady state solutions in a model of a cholesteric liquid crystal sample','Bifurcating solutions in a non-homogeneous boundary value problem','Mottram','Xayxanadasy','Grinfeld','cholesteric','pendulum','time map','time-map','complementary','incomplete beta']
selection=[];screens=[]
for name,prefix,repo,head in [('blueprint','Blueprint/','the-omega-institute/trureturing',O),('problems','Problems/','the-omega-institute/trureturing',O),('openai-tree','','openai/math',A)]:
 p=R/(name+'.json')
 if not p.exists():continue
 d=json.loads(p.read_text());assert d.get('truncated') is False
 paths=[r['path'] for r in d['tree'] if r['type']=='blob']
 hits=[s for s in paths if any(t in s.lower() for t in ['pendul','time_map','timemap','cholester','incompletebeta','incomplete_beta','elliptictail'])]
 screens.append(dict(tree=name,total_paths=len(paths),sha256=sha(p),truncated=False,topic_paths=hits))
 for s in hits:
  if not s.endswith(('.md','.tex','.lean','.cs')):continue
  # Select explanatory bodies plus exact-result Lean texts, not generated proof code.
  if s.endswith('.cs') or (s.endswith('.lean') and not s.endswith('Result.lean')):continue
  url=f'https://raw.githubusercontent.com/{repo}/{head}/{prefix}{s}';n='body-'+hashlib.sha256(url.encode()).hexdigest()[:16]+pathlib.Path(s).suffix
  b=get(n,url)
  if b is not None:selection.append(dict(path=prefix+s,url=url,file=n,sha256=hashlib.sha256(b).hexdigest(),matches=[a for a in aliases if a.lower() in b.decode(errors='replace').lower()]))
delta=json.loads((R/'delta.json').read_text());patches=[]
for f in delta.get('files',[]):
 text=f.get('patch','');patches.append(dict(path=f['filename'],has_patch='patch'in f,matches=[a for a in aliases if a.lower() in text.lower()]))
(R/'registry-topic-screen.json').write_text(json.dumps(dict(aliases=aliases,trees=screens,bodies=selection,known_delta_patches=patches),indent=2))
(R/'retrievals.json').write_text(json.dumps(log,indent=2))
print(json.dumps(dict(trees=screens,bodies=selection,retrieval_errors=[r for r in log if 'error'in r]),indent=2))
