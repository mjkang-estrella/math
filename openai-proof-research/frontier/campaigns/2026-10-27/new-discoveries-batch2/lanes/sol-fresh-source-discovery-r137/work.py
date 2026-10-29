import sys,json,hashlib,urllib.request,datetime,gzip,re,os
from pathlib import Path
L=Path(__file__).resolve().parent
R=L.parents[5]
def sha(b):return hashlib.sha256(b).hexdigest()
if sys.argv[1]=='fetch':
 for name,url in [x.split('=',1) for x in sys.argv[2:]]:
  rec={'name':name,'url':url,'utc':datetime.datetime.now(datetime.timezone.utc).isoformat()}
  try:
   with urllib.request.urlopen(urllib.request.Request(url,headers={'User-Agent':'research-source-audit/1.0'}),timeout=40) as f:
    b=f.read(16000000);rec.update(status=f.status,final_url=f.url,bytes=len(b),sha256=sha(b));(L/'sources'/name).write_bytes(b)
  except Exception as e:rec['error']=str(e)
  with (L/'http.jsonl').open('a') as f:f.write(json.dumps(rec)+'\n')
  print(rec)
elif sys.argv[1]=='history':
 p=re.compile(rb'centrally[ -]essential|nil.clean.{0,35}(matri|exchange)|Calugareanu|C\xc4\x83lug\xc4\x83reanu|Tuganbaev|2204[.]12127|2607[.]14270|anstim[.]2026[.]00019',re.I)
 old=L.parent/'sol-fresh-source-discovery-r133/history-aliases.jsonl.gz'
 names={'summary.md','discovery.md','proof.md','review.md','decision.md'}
 known={};selected={};changed=[];hits=[]
 with gzip.open(old,'rt') as f:
  for line in f:
   h,path=json.loads(line)
   if Path(path).name.lower() in names and not any(x in path.split('/') for x in ['extracted','copy','fresh','replay','history','inputs','evidence']):known[path]=h
 for root,ds,fs in os.walk(R):
  ds[:]=[d for d in ds if d not in {'.git','.lake','node_modules','__pycache__','extracted','fresh','replay','inputs','evidence','history'} and Path(root)/d!=L]
  for name in fs:
   if name.lower() not in names:continue
   f=Path(root)/name;path=str(f.relative_to(R));b=f.read_bytes();h=sha(b)
   if b'\0' in b:continue
   selected.setdefault(h,[]).append(path)
   if known.get(path)!=h:changed.append(path)
   if p.search(b):hits.append({'path':path,'sha256':h,'matches':[{'offset':m.start(),'text':b[max(0,m.start()-120):m.end()+250].decode(errors='replace')} for m in p.finditer(b)]})
 (L/'history-hits.json').write_text(json.dumps(hits,indent=2))
 (L/'history-receipt.json').write_text(json.dumps(dict(pattern=p.pattern.decode(),retained_index=str(old),retained_index_sha256=sha(old.read_bytes()),original_roles=sorted(names),unique_bodies=len(selected),paths=sum(map(len,selected.values())),aliases=selected,new_or_changed_paths=changed,matching_paths=len(hits),global_hit_cutoff=None,complete_bodies_queried=True,limits='Original named report roles only; generated copy/input/evidence/replay directories excluded by role, not date. Original r111-r113 included. Not every source/code body, not semantic absence.'),indent=2))
 print('history',len(selected),'bodies',len(hits),'matching paths',len(changed),'new/changed')
 for h in hits:print(h['path'])
elif sys.argv[1]=='context':
 b=L.parents[1]
 out=[]
 for name in ['ledger.json','prior-campaign-context.json','NEXT.md']:
  f=b/name;data=f.read_bytes();out.append(dict(path=str(f),sha256=sha(data),bytes=len(data)))
  if name.endswith('.json'):
   j=json.loads(data);print(name,list(j) if isinstance(j,dict) else len(j))
   if name=='ledger.json':print([(a.get('number'),a.get('title')) for a in j['accepted']])
  else:print(data.decode()[-13000:])
 (L/'context-receipts.json').write_text(json.dumps(out,indent=2))
elif sys.argv[1]=='registry':
 for name in ['omega-head.json','openai-head.json']:
  j=json.loads((L/'sources'/name).read_bytes());print(name,j['sha'],j['commit']['committer']['date'])
 print('retained delta receipts (qualified scope only):')
 for n in [133,134]:
  f=L.parent/f'sol-fresh-source-discovery-r{n}/registry-delta-receipt.json';j=json.loads(f.read_bytes());print(n,[(k,v) for k,v in j.items() if not isinstance(v,(dict,list))])
elif sys.argv[1]=='delta':
 j=json.loads((L/'sources/omega-compare.json').read_bytes())
 r={k:j.get(k) for k in ['status','ahead_by','behind_by','total_commits']}
 r.update(base='8a9f34a98b9b36553571808bf4187356a94a25ae',head='aa026efa802f4361758b827d6b68231ac353948f',merge_base=j['merge_base_commit']['sha'],commits=len(j['commits']),files=len(j['files']),paths=[f['filename'] for f in j['files']],semantic_clearance=False)
 r['caps_ok']=r['commits']==r['total_commits'] and r['files']<300 and r['commits']<250
 r['ancestry_ok']=r['merge_base']==r['base'] and j['status']=='ahead'
 (L/'registry-delta-receipt.json').write_text(json.dumps(r,indent=2));print(json.dumps(r,indent=2))
elif sys.argv[1]=='aliases':
 j=json.loads((L/'history-receipt.json').read_bytes());p=re.compile(rb'2204[.]12127|anstim[.]2021[.]00013|anstim[.]2022[.]00007|anstim[.]2026[.]00019|centrally essential rings and semirings|are nil.clean.{0,25}integral matrices|on a conjecture concerning.{0,25}nil.clean',re.I)
 hits=[];drift=[];n=0
 for h,paths in j['aliases'].items():
  f=R/paths[0];b=f.read_bytes();n+=1
  if sha(b)!=h:drift.append(paths[0])
  if p.search(b):hits.append(dict(path=paths[0],sha256=sha(b),matches=[m.group().decode(errors='replace') for m in p.finditer(b)]))
 for name in ['ledger.json','prior-campaign-context.json']:
  f=L.parents[1]/name;b=f.read_bytes()
  if p.search(b):hits.append(dict(path=str(f),matches=[m.group().decode(errors='replace') for m in p.finditer(b)]))
 r=dict(complete_representative_bodies=n,pattern=p.pattern.decode(),hits=hits,drift=drift,global_cutoff=None,context_complete_bodies_queried=['ledger.json','prior-campaign-context.json'])
 (L/'exact-alias-receipt.json').write_text(json.dumps(r,indent=2));print(r)
