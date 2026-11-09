import os,sys,json,hashlib,pathlib,subprocess,datetime
L=pathlib.Path(__file__).resolve().parent
B=L.parent.parent
R=B.parents[3]
def sha(p): return hashlib.sha256(p.read_bytes()).hexdigest()
def save(p,x):
 p=L/p;p.parent.mkdir(parents=True,exist_ok=True);p.write_text(x if isinstance(x,str) else json.dumps(x,indent=2))
if sys.argv[1]=='init':
 for n in ['AGENTS.md','ledger.json','prior-campaign-context.json']:
  save('administrative/'+n,(B/n).read_text())
 save('administrative-snapshot.json',{'utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'files':{n:sha(B/n) for n in ['AGENTS.md','ledger.json','prior-campaign-context.json']}})
 save('failures/inventory-memory.txt','Initial recursive rg --files capture under 512MiB AS raised MemoryError. No caps raised. Replaced with bounded two-level listings. Original traceback recorded in tool transcript.\n')
 paths=[str(p) for base in [R/'sources/cache',R/'frontier/sources',B/'lanes'] for d in base.iterdir() if d.is_dir() for p in d.iterdir() if p.is_file() and p.suffix in ['.txt','.tex','.html','.md','.json']]
 save('inventory.txt','\n'.join(paths))
 print('root',R,'inventory',len(paths));print('\n'.join(paths[-60:]))
elif sys.argv[1]=='list':
 for base in [R/'sources/cache',R/'frontier/sources']:
  print(str(base));print('\n'.join(p.name for p in list(base.iterdir())[:180]))
 for name in ['root-focused-r275-disposition','root-scout-r272-disposition','root-scout-r274-disposition','root-scout-r277-disposition','sol-wide-finite-arithmetic-source-r272','sol-wide-specialist-arithmetic-scout-r274']:
  d=B/'lanes'/name
  print(name, [p.name for p in d.iterdir() if p.is_file()])
elif sys.argv[1]=='read':
 for s in sys.argv[2:]:
  p=pathlib.Path(s);p=p if p.is_absolute() else B/'lanes'/p
  h=sha(p)
  with (L/'bindings.jsonl').open('a') as f:f.write(json.dumps({'path':str(p),'sha256':h,'size':p.stat().st_size,'utc':datetime.datetime.now(datetime.timezone.utc).isoformat()})+'\n')
  print('\nFILE',p,'HASH',h);print(p.read_text()[:24000]);assert sha(p)==h
elif sys.argv[1]=='names':
 paths=(L/'inventory.txt').read_text().splitlines()
 terms=sys.argv[2:]
 for s in paths:
  if any(t.lower() in s.lower() for t in terms): print(s)
elif sys.argv[1]=='registry':
 d=R/'frontier/campaigns/2026-10-26/new-discoveries/lanes/pi-euler-turan-final-review/fresh/trureturing'
 print('root',d);print('\n'.join(p.name for p in sorted((d/'Problems').glob('*.md'))))
elif sys.argv[1]=='questions':
 d=R/'frontier/campaigns/2026-10-26/new-discoveries/lanes/pi-euler-turan-final-review/fresh/trureturing'
 names=['agoh-alternating-numerator-characterization','allouche-shallit-2021-sixfold-evil-odious','amdeberhan-chen-moll-sagan-2014-reciprocal-tail-floor-conjecture-4-6','benjamini-helman-tov-zhukovskii-2023-noisy-voter-repetition-variance','bianchi-collet-magnanini-2022-ergm-ghs-marginal','briet-harremoes-2009-trace-exp-exponential-convexity','tarnauceanu-2024-reciprocal-subgroup-orders','somer-krizek-uniform-subsequence-conjecture','rognone-nicosia-2023-square-cluster-exit-time-refutation','random-zeckendorf-game-gaussianity','sitnik-1993-exponential-remainder-differences','baricz-ponnusamy-vuorinen-2011-gamma-gamma-nbu']
 save('selected.json',names)
 refs=[]
 for n in names:
  p=d/'Problems'/(n+'.md');h=sha(p);refs.append({'path':str(p),'sha256':h,'size':p.stat().st_size})
 save('question-bindings.json',refs)
 for q in refs:
  p=pathlib.Path(q['path']);assert sha(p)==q['sha256'];print('\nFILE',p.name);print(p.read_text()[:16000]);assert sha(p)==q['sha256']
elif sys.argv[1]=='compact':
 for q in json.loads((L/'question-bindings.json').read_text()):
  p=pathlib.Path(q['path']);assert sha(p)==q['sha256'];s=p.read_text()
  print('\nFILE',p.name)
  for title in ['Problem','Route','Evidence']:
   key='## '+title;start=s.find(key);end=s.find('\n## ',start+1);print(s[start:end if end!=-1 else None][:3400])
elif sys.argv[1]=='primary':
 import urllib.request,urllib.error,re
 refs=json.loads((L/'question-bindings.json').read_text());access=[]
 for q in refs:
  s=pathlib.Path(q['path']).read_text();m=re.search(r'^url: (.+)$',s,re.M)
  if not m:continue
  url=m[1].strip();url=re.sub(r'arxiv.org/abs/','arxiv.org/pdf/',url)
  row={'url':url,'utc':datetime.datetime.now(datetime.timezone.utc).isoformat()}
  try:
   with urllib.request.urlopen(urllib.request.Request(url,headers={'User-Agent':'research-source-audit/1.0'}),timeout=15) as f:
    data=f.read(12000000);row.update(status=f.status,final_url=f.url)
   if not data.startswith(b'%PDF'):raise ValueError('not PDF; no challenge retry')
   p=L/'primary'/(pathlib.Path(q['path']).stem+'.pdf');p.parent.mkdir(exist_ok=True);p.write_bytes(data);h=sha(p)
   row.update(path=str(p),sha256=h,size=len(data));save('primary-access.json',access+[row])
   out=p.with_suffix('.txt');subprocess.run(['pdftotext','-layout',str(p),str(out)],check=True);assert sha(p)==h
   row['text_sha256']=sha(out)
  except Exception as e:row['error']=str(e)
  access.append(row);save('primary-access.json',access);print(row['url'],row.get('status'),row.get('error','OK'),flush=True)
elif sys.argv[1]=='gate':
 import re
 d=R/'frontier/campaigns/2026-10-26/new-discoveries/lanes/pi-euler-turan-final-review/fresh/trureturing'
 terms=['agoh','evil.odious','reciprocal.tail','noisy.voter','ghs','harrem','subgroup.order','somer','square.cluster','zeckendorf','sitnik','gamma.gamma']
 pats=[re.compile(x,re.I) for x in terms];refs=[];hits=[]
 files=list((d/'Problems').glob('*.md'))+[p for lane in (B/'lanes').iterdir() if lane.is_dir() and lane!=L for p in lane.iterdir() if p.is_file() and p.name in ['SUMMARY.md','SCOUTING.md','discovery.md','review.md','REVIEW.md','STATUS.md']]
 for p in files:
  if p.stat().st_size>500000:continue
  h=sha(p);refs.append({'path':str(p),'sha256':h,'size':p.stat().st_size});s=p.read_text(errors='replace')
  matched=[terms[i] for i,pat in enumerate(pats) if pat.search(s)]
  if matched:
   snippets=[line[:700] for line in s.splitlines() if any(pat.search(line) for pat in pats)]
   hits.append({'path':str(p),'terms':matched,'snippets':snippets[:14]})
  assert sha(p)==h
 save('semantic-search-inventory.json',refs);save('semantic-search-hits.json',hits)
 print('searched',len(refs),'hits',len(hits))
 for hit in hits:
  if 'zeckendorf' in hit['terms'] or 'harrem' in hit['terms']:print(json.dumps(hit))
 # Freeze concrete theorem/proof modules before any scientific read.
 proof=[]
 for q in json.loads((L/'question-bindings.json').read_text()):
  s=pathlib.Path(q['path']).read_text()
  paths=set(re.findall(r'D5/[\w/]+\.lean',s))
  for m in re.findall(r'^  - (D5/[^\n]+)',s,re.M):
   m=m.strip().removesuffix('.result');paths.add(m+'.lean')
  for path in paths:
   p=d/path
   if p.is_file():proof.append({'family':pathlib.Path(q['path']).stem,'path':str(p),'sha256':sha(p),'size':p.stat().st_size})
 save('proof-bindings.json',proof)
 for q in proof:
  p=pathlib.Path(q['path']);assert sha(p)==q['sha256'];s=p.read_text();print('\nPROOF',q['family'],p.relative_to(d),len(s));print(s[:1100]);print(s[-4300:]);assert sha(p)==q['sha256']
elif sys.argv[1]=='inspect':
 import re
 for n in sys.argv[2:]:
  for q in json.loads((L/'question-bindings.json').read_text()):
   if n in q['path']:
    p=pathlib.Path(q['path']);assert sha(p)==q['sha256'];print(p.name);print(p.read_text()[:12500]);assert sha(p)==q['sha256']
elif sys.argv[1]=='excerpts':
 import re
 rows=json.loads((L/'primary-access.json').read_text())
 for q in rows:
  if 'path' not in q:continue
  p=pathlib.Path(q['path']).with_suffix('.txt');assert sha(p)==q['text_sha256'];s=p.read_text()
  print('\nPRIMARY',p.name);print(s[:350])
  matches=list(re.finditer(r'Conjecture|Question|conjecture|Problem 11|NBU|exponential.convex',s))
  for m in matches[-5:]:print(s[max(0,m.start()-180):m.start()+1050])
  assert sha(p)==q['text_sha256']
elif sys.argv[1]=='fetchone':
 import urllib.request
 url=sys.argv[2];name=sys.argv[3];row={'url':url,'utc':datetime.datetime.now(datetime.timezone.utc).isoformat()}
 try:
  with urllib.request.urlopen(url,timeout=15) as f:data=f.read(10000000);row['status']=f.status
  p=L/'primary'/name;p.write_bytes(data);row.update(path=str(p),sha256=sha(p),size=len(data))
  if data.startswith(b'%PDF'):
   subprocess.run(['pdftotext','-layout',str(p),str(p.with_suffix('.txt'))],check=True);row['text_sha256']=sha(p.with_suffix('.txt'))
 except Exception as e:row['error']=str(e)
 save('access-'+name+'.json',row);print(row)
elif sys.argv[1]=='view':
 import re
 p=L/sys.argv[2];h=sha(p)
 with (L/'bindings.jsonl').open('a') as f:f.write(json.dumps({'path':str(p),'sha256':h,'size':p.stat().st_size})+'\n')
 s=p.read_text();print(s[:1500]);count=0
 for m in re.finditer(sys.argv[3],s,re.I):
  print(s[max(0,m.start()-200):m.start()+1900]);count+=1
  if count>=8:break
 assert sha(p)==h
elif sys.argv[1]=='endpoints':
 import re
 for q in json.loads((L/'proof-bindings.json').read_text()):
  if q['family']=='random-zeckendorf-game-gaussianity' or 'ConceptDynamics' in q['path']:continue
  p=pathlib.Path(q['path']);assert sha(p)==q['sha256'];s=p.read_text();print('\n',q['family'],p.name)
  for pat in [r'def (?:fullClaim|claim)\b',r'theorem result\b']:
   m=re.search(pat,s)
   if m:print(s[m.start():m.start()+1450])
  assert sha(p)==q['sha256']
