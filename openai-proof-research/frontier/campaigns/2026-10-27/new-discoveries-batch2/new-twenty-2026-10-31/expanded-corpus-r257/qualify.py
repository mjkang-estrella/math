import pathlib,json,re,hashlib,resource
resource.setrlimit(resource.RLIMIT_CPU,(120,120));resource.setrlimit(resource.RLIMIT_AS,(6*1024**3,6*1024**3))
L=pathlib.Path(__file__).resolve().parent;C=L.parent;D=json.loads((L/'literal-records.json').read_text());ids='|'.join(D)
pat=re.compile(ids+r'|queen|polynomial.positivity|graph.family|357910|331498|330695|331097',re.I)
hist=[]
for p in list(C.glob('*/*.md'))+list(C.glob('*/*results.json'))+[C/'ledger.json',C/'STATUS.md']:
 if L in p.parents or not p.is_file() or p.stat().st_size>2500000:continue
 if p.name not in ['SUMMARY.md','results.json','REVIEW.md','AGENTS.md','ledger.json','STATUS.md'] and not re.search('reject|adjudicat|protected',p.name,re.I):continue
 s=p.read_text(errors='replace');ms=[(i,t) for i,t in enumerate(s.splitlines(),1) if pat.search(t)]
 if ms:hist.append({'path':str(p),'sha256':hashlib.sha256(p.read_bytes()).hexdigest(),'matches':ms})
(L/'history-excerpts.json').write_text(json.dumps(hist,indent=2));print('history matches',len(hist))
for x in hist:
 for n,t in x['matches']:
  if re.search(ids,t): print(x['path'].split('/')[-2],n,t[:500])
inv={};jobs=[]
for p in L.glob('*.abs.html'):
 s=p.read_text();a=p.name.split('.abs')[0];vs=sorted(set(re.findall(re.escape(a)+r'v(\d+)',s)),key=int)
 inv[a]={'versions':vs,'journal_metadata':re.findall(r'<meta name="citation_(?:doi|journal_title|date)" content="([^"]+)"',s)}
 for v in vs:jobs.append((a+'v'+v+'.pdf','https://arxiv.org/pdf/'+a+'v'+v))
(L/'version-jobs.json').write_text(json.dumps(jobs));(L/'body-inventory.json').write_text(json.dumps(inv,indent=2))
