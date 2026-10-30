import sys,json,hashlib,re,datetime,urllib.request,subprocess
from pathlib import Path
L=Path(__file__).resolve().parent; B=L.parents[1]; R=L.parents[5]
def sha(b):return hashlib.sha256(b).hexdigest()
def save(n,j):(L/n).write_text(json.dumps(j,indent=2,ensure_ascii=False)+'\n')
if sys.argv[1]=='context':
 out={}
 for n in ['ledger.json','prior-campaign-context.json','NEXT.md']:
  b=(B/n).read_bytes();(L/('context-'+n)).write_bytes(b)
  out[n]={'sha256':sha(b),'bytes':len(b),'text':b.decode()}
 save('context-reading.json',out)
 print([(n,v['bytes']) for n,v in out.items()])
elif sys.argv[1]=='history':
 old=L.parent/'sol-fresh-source-discovery-r143/history-receipt.json';j=json.loads(old.read_bytes())
 known={p:h for h,ps in j['aliases'].items() for p in ps};paths=set(known)
 for lane in (B/'lanes').iterdir():
  if lane==L or not lane.is_dir():continue
  for f in lane.iterdir():
   if f.is_file() and f.name.lower() in {'summary.md','discovery.md','proof.md','review.md','decision.md'}:paths.add(str(f.relative_to(R)))
 pat=re.compile(sys.argv[2],re.I);aliases={};hits=[];changed=[];missing=[]
 for p in sorted(paths):
  f=R/p
  if not f.is_file():missing.append(p);continue
  b=f.read_bytes();h=sha(b);aliases.setdefault(h,[]).append(p)
  if known.get(p)!=h:changed.append(p)
  if pat.search(b.decode(errors='replace')):
   b2=f.read_bytes();assert b==b2
   dest=L/'reopened'/sys.argv[3]/str(len(hits));dest.parent.mkdir(exist_ok=True,parents=True);dest.write_bytes(b2)
   hits.append({'path':p,'sha256':h,'bytes':len(b),'copy':str(dest.relative_to(L))})
 context={n:bool(pat.search((L/('context-'+n)).read_text())) for n in ['ledger.json','prior-campaign-context.json','NEXT.md']}
 save('history-'+sys.argv[3]+'.json',dict(retained=str(old),retained_sha256=sha(old.read_bytes()),pattern=pat.pattern,aliases=aliases,hits=hits,changed=changed,missing=missing,context=context,full_bodies=True,cutoff=None,limits='Original report roles from qualified r143 plus new immediate batch originals; retained r111-r113 science. No generated echo inventory; lexical screen only, no semantic absence.'))
 print('unique bodies',len(aliases),'hits',len(hits),'changed',len(changed),context);print(json.dumps(hits))
elif sys.argv[1]=='fetch':
 for arg in sys.argv[2:]:
  name,url=arg.split('=',1);r=dict(name=name,url=url,utc=datetime.datetime.now(datetime.timezone.utc).isoformat())
  try:
   with urllib.request.urlopen(urllib.request.Request(url,headers={'User-Agent':'mathematical-source-research/1.0'}),timeout=30) as f:
    b=f.read(12000001)
    if len(b)>12000000:raise ValueError('12 MB response cap')
    (L/'sources'/name).write_bytes(b);r.update(status=f.status,final_url=f.url,bytes=len(b),sha256=sha(b))
  except Exception as e:r['error']=str(e)
  with (L/'http.jsonl').open('a') as f:f.write(json.dumps(r)+'\n')
  print(r)
elif sys.argv[1]=='text':
 for n in sys.argv[2:]:
  p=subprocess.run(['pdftotext','-layout',str(L/'sources'/n),str(L/'sources'/n.replace('.pdf','.txt'))],capture_output=True);print(n,p.returncode,p.stderr.decode())
elif sys.argv[1]=='registry':
 out=[];pat=re.compile(r'rogers|shephard|fradelizi|manui|zono|firey|orlicz',re.I)
 for n in ['omega-library-tree.json','omega-problems-tree.json','omega-docs-tree.json']:
  p=L.parent/'sol-fresh-source-discovery-r143/sources'/n;j=json.loads(p.read_bytes())
  hits=[x for x in j['tree'] if pat.search(x['path'])]
  out.append(dict(path=str(p),sha256=sha(p.read_bytes()),truncated=j.get('truncated'),hits=hits))
 save('registry-path-screen.json',out);print(json.dumps(out,indent=2))
elif sys.argv[1]=='baseline':
 import gzip
 out=[];pat=re.compile(r'rogers|shephard|fradelizi|manui|firey|zono|orlicz',re.I)
 for name in ['omega-tree.txt.gz','openai-tree.txt.gz']:
  p=L.parent/'root-edge-irregulator-final-freeze-r1'/name;hh=hashlib.sha256();hits=[];count=0
  with gzip.open(p,'rb') as f:
   for line in f:
    hh.update(line);count+=1
    if pat.search(line.decode()):hits.append(line.decode().strip())
  out.append(dict(path=str(p),uncompressed_sha256=hh.hexdigest(),lines=count,hits=hits))
 save('baseline-path-screen.json',out);print(json.dumps(out,indent=2))
elif sys.argv[1]=='delta':
 p=L/'sources/compare-second.json';j=json.loads(p.read_bytes());old=L.parent/'sol-fresh-source-discovery-r140/registry-delta-receipt.json'
 save('registry-delta-receipt.json',dict(first_interval=dict(path=str(old),sha256=sha(old.read_bytes()),receipt=json.loads(old.read_bytes()),limits='300-path cap; r140 closes only three source-facing Markdown paths in stated scopes'),second_interval=dict(sha256=sha(p.read_bytes()),status=j['status'],base=j['base_commit']['sha'],merge_base=j['merge_base_commit']['sha'],commits=len(j['commits']),total_commits=j['total_commits'],files=len(j['files']),paths=[x['filename'] for x in j['files']],cap_hit=len(j['files'])==300),semantic_clearance=False,head_chasing=False))
 print('second interval',len(j['commits']),j['total_commits'],'commits;',len(j['files']),'paths; semantic clearance FALSE')
elif sys.argv[1]=='inspect':
 j=json.loads((L/'sources/omega-geometry.json').read_bytes());print('geometry truncated',j.get('truncated'));print('\n'.join(x['path'] for x in j['tree'] if x['path'].endswith('.md')))
 for n in ['fc-pr.json','fc-files.json']:
  j=json.loads((L/'sources'/n).read_bytes())
  if isinstance(j,dict):print(n,{k:j.get(k) for k in ['title','body','created_at','merged_at','merge_commit_sha']})
  else:
   for x in j:print(n,x['filename'],x.get('patch'),x.get('raw_url'))
elif sys.argv[1]=='chronology':
 out={}
 for n in ['prior-commit.json','omega-fixed-commit.json']:
  j=json.loads((L/'sources'/n).read_bytes());out[n]={k:j['commit'][k] for k in ['author','committer','message']};out[n]['sha']=j['sha']
 print(json.dumps(out,indent=2));save('chronology.json',out)
