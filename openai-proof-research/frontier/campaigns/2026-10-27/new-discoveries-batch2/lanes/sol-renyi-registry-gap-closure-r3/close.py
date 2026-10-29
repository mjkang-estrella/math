import pathlib,json,hashlib,datetime,sys,re,urllib.request,urllib.error
L=pathlib.Path(__file__).resolve().parent; B=L.parent
if len(sys.argv)<2:sys.argv.append('library')
def sha(p):
 h=hashlib.sha256()
 with p.open('rb') as f:
  for b in iter(lambda:f.read(65536),b''):h.update(b)
 return h.hexdigest()
def save(n,d): (L/n).write_text(json.dumps(d,indent=2,ensure_ascii=False)+'\n')
def load(p): return json.loads(p.read_bytes())
def audit(stage):
 out={}
 for fr,src in [('root-renyi-threshold-review-freeze-r1','sol-fresh-source-discovery-r111'),('root-renyi-preliminary-adoption-r1','sol-renyi-threshold-preliminary-review-r1'),('root-renyi-prior-adoption-r2','sol-renyi-threshold-current-prior-review-r2')]:
  m=B/fr/'review-freeze.json';rows=[]
  for p,h in load(m).items():
   f=B/src/p;g=sha(f);rows.append(dict(path=str(f),expected=h,actual=g,match=g==h,bytes=f.stat().st_size))
  out[src]=dict(manifest_sha256=sha(m),rows=rows,all_match=all(r['match'] for r in rows))
 save(stage+'.json',out);assert all(x['all_match'] for x in out.values())
def fetch(url,dest,cap=24000000):
 if (L/'STOP-NETWORK.json').exists(): raise RuntimeError('network stopped by first403/429')
 row=dict(url=url,utc=datetime.datetime.now(datetime.timezone.utc).isoformat(),dest=str(dest.relative_to(L)))
 try:
  with urllib.request.urlopen(urllib.request.Request(url,headers={'User-Agent':'bounded-public-registry-review/1.0'}),timeout=25) as r:
   row.update(status=r.status,headers=dict(r.headers)); b=r.read(cap+1)
   if len(b)>cap:raise ValueError('response size cap')
   dest.parent.mkdir(parents=True,exist_ok=True);dest.write_bytes(b);row.update(bytes=len(b),sha256=sha(dest))
 except Exception as e:
  row['error']=repr(e)
  if isinstance(e,urllib.error.HTTPError):row.update(status=e.code,headers=dict(e.headers))
 with (L/'http.jsonl').open('a') as f:f.write(json.dumps(row)+'\n')
 if row.get('status') in (403,429):save('STOP-NETWORK.json',row)
 if 'error' in row:raise RuntimeError(row)
 return dest
PAT=re.compile(r'2510[.]09206|\bFu\b.{0,12}\bLi\b|R[eé]nyi|reverse.{0,20}(?:EPI|entropy.power)|log[ -]?concav|truncat.{0,40}exponential|exponential.{0,40}truncat|entropy.{0,20}increment|self[ -]?convolution|positive[ -]?sum',re.I)
def screen(p):
 # Full selected body scanned, individual lines/excerpts bounded only in output.
 text=p.read_text(errors='replace'); decoded=[];opaque=[]
 try:
  obj=json.loads(text)
  def walk(x,key=''):
   if isinstance(x,dict):
    for k,v in x.items():walk(v,k)
   elif isinstance(x,list):
    for v in x:walk(v,key)
   elif isinstance(x,str):
    decoded.append(x)
    if len(x)>300 and re.fullmatch(r'[A-Za-z0-9+/=\s]+',x):opaque.append(dict(key=key,chars=len(x),prefix=x[:50]))
  walk(obj)
 except (ValueError,RecursionError):pass
 s=text+'\n'+'\n'.join(decoded)
 hits=[s[max(0,m.start()-180):m.end()+350] for m in PAT.finditer(s)]
 return dict(bytes=p.stat().st_size,sha256=sha(p),json_strings_decoded=len(decoded),opaque_candidates=opaque,hits=hits[:40],hit_count=len(hits),semantic_scan_chars=len(s))
def compare(a,z):
 dest=L/'comparisons'/(a+'...'+z+'.json')
 if not dest.exists():fetch('https://api.github.com/repos/the-omega-institute/trureturing/compare/'+a+'...'+z,dest)
 d=load(dest);assert d['base_commit']['sha']==a and d['merge_base_commit']['sha']==a and d['status']=='ahead';assert len(d['commits'])==d['total_commits'] and d['commits'][-1]['sha']==z
 if len(d['files'])>=300:
  cs=d['commits'];by={c['sha']:c for c in cs};chain=[];cur=z
  while cur in by:chain.append(cur);cur=by[cur]['parents'][0]['sha']
  assert cur==a and len(chain)>1;mid=chain[len(chain)//2];return compare(a,mid)+compare(mid,z)
 return [dict(base=a,end=z,commits=[dict(sha=c['sha'],parents=[p['sha'] for p in c['parents']],utc=c['commit']['committer']['date']) for c in d['commits']],file_count=len(d['files']),truncated=False,sha256=sha(dest),response=str(dest.relative_to(L)),files=d['files'])]
if sys.argv[1]=='init':
 audit('before')
 rows=[]
 for i in range(100,112):
  s=B/('sol-fresh-source-discovery-r'+str(i))/'sources'
  for p in sorted(s.glob('*delta*.json')):
   try:
    d=load(p)
    if 'base_commit' in d:rows.append(dict(path=str(p),base=d['base_commit']['sha'],end=d.get('commits',[{}])[-1].get('sha') if d.get('commits') else d['base_commit']['sha'],commits=d.get('total_commits'),files=len(d.get('files',[])),sha256=sha(p)))
   except Exception as e:print(str(p),str(e)[:100])
 save('cached-chain.json',rows)
 old=load(B/'sol-fresh-source-discovery-r100/sources/registry-delta-0.json');cs=old['commits'];by={c['sha']:c for c in cs};chain=[];cur=cs[-1]['sha']
 while cur in by:chain.append(cur);cur=by[cur]['parents'][0]['sha']
 assert cur==old['base_commit']['sha'];mid=chain[len(chain)//2]
 res=compare(old['base_commit']['sha'],mid)+compare(mid,cs[-1]['sha']);save('split-intervals.json',res)
 print('split',[(r['file_count'],len(r['commits'])) for r in res],flush=True)
elif sys.argv[1]=='screen':
 print(json.dumps(screen(pathlib.Path(sys.argv[2])),ensure_ascii=False,indent=2))
elif sys.argv[1]=='plan':
 splits=load(L/'split-intervals.json'); intervals=splits[:];cur=splits[-1]['end']
 for r in load(L/'cached-chain.json'):
  if r['base']!=cur or r['end']==cur:continue
  p=pathlib.Path(r['path']);d=load(p);assert sha(p)==r['sha256'];assert len(d['files'])<300 and len(d['commits'])==d['total_commits'];assert d['merge_base_commit']['sha']==cur and d['status']=='ahead'
  intervals.append(dict(base=cur,end=r['end'],commits=[dict(sha=c['sha'],parents=[p['sha'] for p in c['parents']],utc=c['commit']['committer']['date']) for c in d['commits']],file_count=len(d['files']),truncated=False,sha256=sha(p),response=str(p),files=d['files']));cur=r['end']
 assert cur=='89cda9c274d1122b7676173296af3047c3b64cd1'
 p=B/'sol-renyi-threshold-current-prior-review-r2/omega-delta.json';d=load(p)
 intervals.append(dict(base=cur,end=d['commits'][-1]['sha'],commits=[dict(sha=c['sha'],parents=[p['sha'] for p in c['parents']],utc=c['commit']['committer']['date']) for c in d['commits']],file_count=len(d['files']),truncated=False,sha256=sha(p),response=str(p),files=d['files']))
 # Parent graph closure proves no missing commit inside each forward ancestry interval.
 for r in intervals:
  known={c['sha'] for c in r['commits']};r['parent_graph_external']=[dict(commit=c['sha'],parent=p) for c in r['commits'] for p in c['parents'] if p not in known and p!=r['base']]
 save('intervals.json',intervals)
 bodies={};patches=[]
 def add(repo,ref,path,reason,blob=None):
  key=repo+'|'+ref+'|'+path
  if key not in bodies:bodies[key]=dict(repo=repo,ref=ref,path=path,reasons=[],blob=blob,status='pending')
  bodies[key]['reasons'].append(reason)
 for i,r in enumerate(intervals):
  for f in r['files']:
   path=f['filename'];patch=f.get('patch','');hits=[m.group() for m in PAT.finditer(path+'\n'+patch)]
   if hits:patches.append(dict(interval=i,path=path,hits=hits,patch=patch[:25000]))
   if 'patch' not in f or hits:
    # Previous version of removals/modifications also checked: deletion can conceal a prior proof.
    if f['status']!='removed':add('the-omega-institute/trureturing',r['end'],path,'missing-patch' if 'patch' not in f else 'semantic-hit',f.get('sha'))
    if f['status']!='added':add('the-omega-institute/trureturing',r['base'],f.get('previous_filename',path),'prior-version '+f['status'])
 baseline={}
 cfg=load(B/'root-edge-irregulator-final-freeze-r1/CURRENT-REGISTRIES.json')
 for repo,name in [('the-omega-institute/trureturing','omega'),('openai/math','openai')]:
  p=B/'root-edge-irregulator-final-freeze-r1'/(name+'-tree.txt');h=hashlib.sha256();count=0;selected=[]
  with p.open('rb') as f:
   for b in f:
    h.update(b);count+=1;s=b.decode().rstrip();meta,path=s.split('\t',1)
    if PAT.search(path) or re.search(r'entropy|convolution',path,re.I):
     selected.append(path);add(repo,cfg[name]['head'],path,'baseline-relevant-path',meta.split()[-1])
  assert h.hexdigest()==cfg[name]['tree_sha256'] and count==cfg[name]['entries']
  baseline[name]=dict(sha256=h.hexdigest(),entries=count,complete=True,selected_paths=selected,head=cfg[name]['head'])
 save('baseline.json',baseline);save('patch-hits.json',patches);save('bodies.json',list(bodies.values()))
 print(json.dumps(dict(intervals=[(r['file_count'],len(r['commits'])) for r in intervals],bodies=len(bodies),baseline={k:len(v['selected_paths']) for k,v in baseline.items()},patch_hits=len(patches))))
elif sys.argv[1]=='bodies':
 rows=load(L/'bodies.json');n=0
 for r in rows:
  if r['status']=='ok':continue
  dest=L/'bodies'/(hashlib.sha256((r['repo']+'|'+r['ref']+'|'+r['path']).encode()).hexdigest()+pathlib.Path(r['path']).suffix)
  url='https://raw.githubusercontent.com/'+r['repo']+'/'+r['ref']+'/'+urllib.parse.quote(r['path'])
  try:
   if not dest.exists():fetch(url,dest)
   r.update(status='ok',source=str(dest.relative_to(L)),url=url,read=screen(dest));data=dest.read_bytes();r['actual_git_blob']='%s'%hashlib.sha1(b'blob '+str(len(data)).encode()+b'\0'+data).hexdigest()
   r['blob_matches']=r['blob'] is None or r['blob']==r['actual_git_blob']
  except Exception as e:r.update(status='error',error=str(e));save('bodies.json',rows);raise
  n+=1;save('bodies.json',rows)
  print(json.dumps(dict(index=n,path=r['path'],bytes=r['read']['bytes'],hits=r['read']['hit_count'],opaque=len(r['read']['opaque_candidates']))),flush=True)
  if n>=int(sys.argv[2]):break
elif sys.argv[1]=='trim':
 rows=load(L/'bodies.json');keep=[];excluded=[]
 for r in rows:
  p=r['path'];base=r['reasons']==['baseline-relevant-path']
  sel=(r['repo'].endswith('trureturing') and p.endswith('.md') and (re.search(r'renyi|entropy.?power|entropy.?increment|truncated.?exponential',p,re.I) or ('Probability/' in p and re.search(r'entropy|convolution|logconcav',p,re.I)))) or (r['repo']=='openai/math' and re.search(r'WeightedRenyi|Heat/(ExactEntropyPower|RenyiFisherBounds)|Entropy/RenyiKernel|Boltzmann/Branching/TruncatedExponential',p))
  if not base or sel:keep.append(r)
  else:excluded.append(dict(repo=r['repo'],path=p,disposition='Outside bounded baseline actual-body selection; path inventory screened, not semantic clearance'))
 save('baseline-unread-limits.json',excluded);save('bodies.json',keep);print('required bodies',len(keep),'baseline',sum(r['reasons']==['baseline-relevant-path'] for r in keep))
