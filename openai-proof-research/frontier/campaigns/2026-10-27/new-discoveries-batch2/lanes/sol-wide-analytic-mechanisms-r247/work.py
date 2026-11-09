import pathlib,hashlib,json,sys,datetime,urllib.request,subprocess
import urllib.parse,xml.etree.ElementTree as ET
L=pathlib.Path(__file__).resolve().parent
B=L.parent.parent
def sha(p): return hashlib.sha256(p.read_bytes()).hexdigest()
def freeze(p,admin=False):
 p=pathlib.Path(p).resolve(); h=sha(p)
 out=L/('administrative' if admin else 'sources')/(h[:12]+'-'+p.name)
 out.parent.mkdir(exist_ok=True); out.write_bytes(p.read_bytes())
 assert sha(p)==h==sha(out)
 rec={'original':str(p),'copy':str(out.relative_to(L)),'sha256':h,'administrative':admin,'time':datetime.datetime.now(datetime.timezone.utc).isoformat()}
 with (L/'provenance.jsonl').open('a') as f:f.write(json.dumps(rec)+'\n')
 return out
if sys.argv[1]=='init':
 for n in ['AGENTS.md','ledger.json','prior-campaign-context.json']:freeze(B/n,True)
 for p in [B.parents[3]/'AGENTS.md',B.parents[3]/'sources/upstream.json']:
  if p.exists():freeze(p,True)
 for name in ['sol-wide-analytic-geometric-scout-r246','sol-independent-analytic-mechanism-scout-r243','sol-wide-new-analysis-r227','sol-fresh-analytic-wide-scout-r219','sol-wide-analysis-scout-r221','sol-wide-analytic-scout-r223']:
  for n in ['SCOUTING.md','SUMMARY.md','discovery.md']:
   p=B/'lanes'/name/n
   if p.exists():
    q=freeze(p); print('\nFROZEN',name,n,'\n',q.read_text()[:24000])
 print('ROOT',[(p.name,p.is_dir()) for p in B.parents[3].iterdir()])
if sys.argv[1]=='search':
 q=sys.argv[2]; url='https://export.arxiv.org/api/query?'+urllib.parse.urlencode({'search_query':q,'start':0,'max_results':45,'sortBy':'relevance'})
 dest=L/('search-'+hashlib.sha256(q.encode()).hexdigest()[:10]+'.xml')
 try:
  data=urllib.request.urlopen(url,timeout=35).read(3000000); dest.write_bytes(data)
  print('SAVED',dest.name,hashlib.sha256(data).hexdigest())
  root=ET.fromstring(data); ns={'a':'http://www.w3.org/2005/Atom'}
  for e in root.findall('a:entry',ns):print(e.findtext('a:id',namespaces=ns),e.findtext('a:title',namespaces=ns),e.findtext('a:summary',namespaces=ns)[:800])
 except Exception as e:
  with (L/'access-failures.jsonl').open('a') as f:f.write(json.dumps({'url':url,'error':str(e)})+'\n')
  print(type(e).__name__,str(e))
if sys.argv[1]=='get':
 for ident in sys.argv[2:]:
  dest=L/'sources'/(ident+'.pdf'); url='https://arxiv.org/pdf/'+ident
  try:
   data=urllib.request.urlopen(url,timeout=35).read(15000000);dest.write_bytes(data)
   h=sha(dest); print('FROZEN',ident,h)
   with (L/'provenance.jsonl').open('a') as f:f.write(json.dumps({'url':url,'copy':str(dest.relative_to(L)),'sha256':h,'time':datetime.datetime.now(datetime.timezone.utc).isoformat()})+'\n')
   subprocess.run(['pdftotext','-layout',str(dest),str(dest.with_suffix('.txt'))],check=True)
   assert sha(dest)==h
   t=dest.with_suffix('.txt'); print('TEXT HASH',sha(t))
   lines=t.read_text().splitlines(); inds=[i for i,l in enumerate(lines) if any(w in l.lower() for w in ['conjecture','open problem','question','problem 1','problem 2'])]
   for i in inds[-25:]:print('\n',i,'\n','\n'.join(lines[max(0,i-2):i+10]))
  except Exception as e:
   with (L/'access-failures.jsonl').open('a') as f:f.write(json.dumps({'url':url,'error':str(e)})+'\n')
   print('FAIL',ident,str(e))
if sys.argv[1]=='history':
 terms=sys.argv[2:]; refs=[]; hits={t:[] for t in terms}
 for d in B.joinpath('lanes').iterdir():
  if d==L:continue
  for n in ['SCOUTING.md','SUMMARY.md','discovery.md','review.md']:
   p=d/n
   if not p.exists():continue
   h=sha(p); refs.append({'path':str(p),'sha256':h})
   # Immutable reference bound before scientific reading; do not copy evidence trees.
   s=p.read_text(errors='replace').lower()
   for t in terms:
    if t.lower() in s:hits[t].append(str(p.relative_to(B)))
   assert sha(p)==h
 (L/'history-references.json').write_text(json.dumps(refs,indent=2))
 (L/'history-hits.json').write_text(json.dumps(hits,indent=2))
 print('VERIFIED',len(refs));print(json.dumps(hits,indent=2))
