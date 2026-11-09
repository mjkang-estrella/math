import pathlib, hashlib, json, sys, datetime, shutil, urllib.request, subprocess
L=pathlib.Path(__file__).resolve().parent
B=L.parent.parent
R=B.parents[3]
def sha(p): return hashlib.sha256(p.read_bytes()).hexdigest()
def freeze(paths,kind='science'):
 d=L/kind;d.mkdir(exist_ok=True)
 index=json.loads((L/'freeze.json').read_text()) if (L/'freeze.json').exists() else []
 for s in paths:
  p=pathlib.Path(s); h=sha(p); q=d/(h[:16]+'-'+p.name)
  if not q.exists(): shutil.copyfile(p,q)
  assert sha(p)==h==sha(q)
  if not any(x['original']==str(p) for x in index):index.append(dict(original=str(p),copy=str(q.relative_to(L)),sha256=h,kind=kind))
 (L/'freeze.json').write_text(json.dumps(index,indent=2))
if sys.argv[1]=='init':
 freeze([B/'ledger.json',B/'prior-campaign-context.json',B/'AGENTS.md',R/'AGENTS.md',R/'sources/upstream.json'],'admin')
 for p in L.parent.iterdir():
  if 'r257' in p.name or 'r259' in p.name:print(p)
 for p in L.parent.iterdir():
  if p.is_dir():
   for q in p.glob('*alias*.json'):
    if q.stat().st_size<300000:print(q)
elif sys.argv[1]=='freeze':freeze(sys.argv[2:])
elif sys.argv[1]=='read':
 for e in json.loads((L/'freeze.json').read_text()):
  if any(x in e['original'] for x in sys.argv[2:]):
   p=L/e['copy']; assert sha(p)==e['sha256']; print('\nFILE',e['original']);print(p.read_text()[:45000])
elif sys.argv[1]=='verify':
 idx=json.loads((L/'freeze.json').read_text()); failures=[]
 for e in idx:
  if e['kind']=='science' and (sha(pathlib.Path(e['original']))!=e['sha256'] or sha(L/e['copy'])!=e['sha256']):failures.append(e['original'])
 print(json.dumps(dict(scientific_references=sum(e['kind']=='science' for e in idx),failures=failures)))
 assert not failures
elif sys.argv[1]=='inventory':
 for p in (L.parent/'sol-wide-analytic-mechanism-scout-r257').iterdir():print(p.name,p.stat().st_size)
 for e in json.loads((L/'freeze.json').read_text()):
  if 'prior-campaign-context' in e['original']:
   j=json.loads((L/e['copy']).read_text()); print(json.dumps(j)[:22000])
elif sys.argv[1]=='fetch':
 log=json.loads((L/'access.json').read_text()) if (L/'access.json').exists() else []
 out=L/'primary';out.mkdir(exist_ok=True)
 for url in sys.argv[2:]:
  if any(x['url']==url for x in log):print('ALREADY ATTEMPTED',url);continue
  row=dict(url=url,utc=datetime.datetime.now(datetime.timezone.utc).isoformat())
  try:
   req=urllib.request.Request(url,headers={'User-Agent':'ResearchSourceAudit/1.0'})
   with urllib.request.urlopen(req,timeout=22) as r:
    data=r.read(12000001);assert len(data)<=12000000
    row.update(status=r.status,final_url=r.url,headers=dict(r.headers))
   p=out/(hashlib.sha256(url.encode()).hexdigest()[:16]+('.pdf' if data.startswith(b'%PDF') else '.html'));p.write_bytes(data)
   row.update(path=str(p.relative_to(L)),sha256=sha(p),bytes=len(data)); print(url,'OK',p.name)
   freeze([p])
  except Exception as ex:row['error']=repr(ex);print(url,row['error'])
  log.append(row);(L/'access.json').write_text(json.dumps(log,indent=2))
elif sys.argv[1]=='extract':
 for p in (L/'primary').glob('*.pdf'):
  q=p.with_suffix('.txt')
  if not q.exists():subprocess.run(['pdftotext','-layout',str(p),str(q)],check=True)
  freeze([q])
elif sys.argv[1]=='snips':
 import re
 for p in (L/'primary').glob('*'):
  if p.suffix not in ['.txt','.html']:continue
  assert any(e['original']==str(p) and e['sha256']==sha(p) for e in json.loads((L/'freeze.json').read_text()))
  t=p.read_text(errors='replace'); print('\nFILE',p.name)
  for m in list(re.finditer(sys.argv[2],t,re.I))[:14]:print(t[max(0,m.start()-220):m.start()+1600])
elif sys.argv[1]=='searchread':
 import re,html
 for p in (L/'primary').glob('*.html'):
  t=p.read_text(); t=html.unescape(re.sub('<[^>]+>',' ',t));t=re.sub(r'\s+',' ',t)
  print(p.name)
  for s in re.split(r'arXiv:',t)[1:]: print(s[:220])
elif sys.argv[1]=='hist':
 e=next(e for e in json.loads((L/'freeze.json').read_text()) if 'history-bindings' in e['original'])
 j=json.loads((L/e['copy']).read_text());print(str(j)[:3500])
elif sys.argv[1]=='screenhistory':
 e=next(e for e in json.loads((L/'freeze.json').read_text()) if 'history-bindings' in e['original'])
 idx=json.loads((L/e['copy']).read_text());rows=[];hits=[];mismatch=[]
 terms=sys.argv[2:]
 for e in idx:
  p=pathlib.Path(e['path'])
  if not p.exists() or sha(p)!=e['sha256']:mismatch.append(str(p));continue
  t=p.read_text(errors='replace'); found=[]
  for term in terms:
   pos=t.lower().find(term.lower())
   if pos>=0:found.append(dict(term=term,excerpt=t[max(0,pos-120):pos+500]))
  assert sha(p)==e['sha256'];rows.append(e)
  if found:hits.append(dict(reference=e,hits=found))
 target=L/'early-history.json'
 if target.exists():target=L/'expanded-history.json'
 target.write_text(json.dumps(dict(terms=terms,verified_references=rows,mismatch=mismatch,hits=hits),indent=2));print('verified',len(rows),'mismatch',len(mismatch));print(json.dumps(hits)[:12000])
elif sys.argv[1]=='body':
 import re
 a=json.loads((L/'access.json').read_text())
 for ident in sys.argv[2:]:
  row=next(x for x in a if x['url'].endswith('/'+ident));p=L/pathlib.Path(row['path']).with_suffix('.txt');t=p.read_text()
  print('\nSOURCE',ident,'\n',t[:11500])
elif sys.argv[1]=='focused':
 import re
 ident,pat=sys.argv[2:4];a=json.loads((L/'access.json').read_text());row=next(x for x in a if x['url'].endswith('/'+ident));p=L/pathlib.Path(row['path']).with_suffix('.txt');t=p.read_text();end=0
 for m in list(re.finditer(pat,t,re.I))[:8]:
  if m.start()<end:continue
  start=max(0,m.start()-150);end=m.start()+int(sys.argv[4] if len(sys.argv)>4 else 2200);print(t[start:end])
elif sys.argv[1]=='methods':
 import re
 pats={'2609.24131':'Proof of Theorem 1.1|Theorem 1.12|Theorem 1.13','2610.20916':'Proof of Theorem 1.1','2609.06223':'Proof of Theorem 1.4|Proof of Theorem 1.6','2610.16904':'\\(M1\\)|Proposition 5.3|Proof of Theorem 2.1','2610.03204':'Proof of Theorem 1.3','2610.07248':'Proof of Theorem 1|Proof of Theorem 2','2610.10229':'Theorem 6.1|Proof of Theorem 6.1','2610.13848':'Proof of Theorem 1.1','2609.11418':'Theorem 1.1|Theorem 1.2|Question 10','2608.30275':'Proof of Theorem 1'}
 rows=[]
 for ident,pat in pats.items():
  row=next(x for x in json.loads((L/'access.json').read_text()) if x['url'].endswith('/'+ident));p=L/pathlib.Path(row['path']).with_suffix('.txt');t=p.read_text();bits=[];end=0
  for match in re.finditer(pat,t):
   if match.start()<end:continue
   end=match.start()+2300;bits.append(t[max(0,match.start()-100):end])
   if len(bits)==3:break
  rows.append(dict(id=ident,pattern=pat,excerpts=bits));print(ident,'\n','\n'.join(bits))
 (L/'method-excerpts.json').write_text(json.dumps(rows,indent=2))
elif sys.argv[1]=='chronology':
 urls=['https://arxiv.org/abs/'+x['url'].rsplit('/',1)[1] for x in json.loads((L/'access.json').read_text()) if '/pdf/' in x['url']]
 print('\n'.join(urls))
