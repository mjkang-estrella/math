import pathlib,hashlib,json,sys,shutil,urllib.request,datetime,subprocess
L=pathlib.Path(__file__).resolve().parent
B=L.parent.parent
def sha(p): return hashlib.sha256(p.read_bytes()).hexdigest()
def freeze(p,d):
 a=sha(p); d.parent.mkdir(parents=True,exist_ok=True); shutil.copyfile(p,d)
 assert a==sha(p)==sha(d)
 return dict(original=str(p),copy=str(d),sha256=a,bytes=p.stat().st_size)
if sys.argv[1]=='init':
 records=[]
 for n in ['AGENTS.md','ledger.json','prior-campaign-context.json']:
  records.append(freeze(B/n,L/'administrative'/n))
 for n in ['sol-pade-breadth-depth-r1','sol-trip-breadth-depth-r1']+[p.name for p in L.parent.iterdir() if any('r'+str(i) in p.name for i in range(213,222))]:
  p=L.parent/n/'SCOUTING.md'
  if p.exists(): records.append(freeze(p,L/'frozen-reports'/n/'SCOUTING.md'))
 (L/'freeze.json').write_text(json.dumps(records,indent=2))
 for r in records:
  if 'SCOUTING' in r['copy']: print('\nSOURCE',r['copy'],'\n',pathlib.Path(r['copy']).read_text()[:16000])
if sys.argv[1]=='fetch':
 url,name=sys.argv[2:4]; out=L/'sources'/name;out.parent.mkdir(exist_ok=True)
 try:
  req=urllib.request.Request(url,headers={'User-Agent':'Mathematical research source check (bounded single request)'})
  with urllib.request.urlopen(req,timeout=35) as f:
   data=f.read(12000000); meta=dict(url=url,final_url=f.url,status=f.status,headers=dict(f.headers),utc=datetime.datetime.now(datetime.timezone.utc).isoformat())
  out.write_bytes(data);meta.update(sha256=sha(out),bytes=len(data));out.with_suffix(out.suffix+'.json').write_text(json.dumps(meta,indent=2));print(meta)
 except Exception as e:
  with (L/'access-failures.jsonl').open('a') as f:f.write(json.dumps(dict(url=url,error=str(e),utc=datetime.datetime.now(datetime.timezone.utc).isoformat()))+'\n')
  print(type(e).__name__,str(e))
if sys.argv[1]=='verify':
 for r in json.loads((L/'freeze.json').read_text()):
  assert sha(pathlib.Path(r['original']))==sha(pathlib.Path(r['copy']))==r['sha256']
 print('originals and frozen reports verified')
if sys.argv[1]=='feed':
 import xml.etree.ElementTree as E
 p=L/'sources'/sys.argv[2]; a=sha(p); root=E.fromstring(p.read_bytes());ns={'a':'http://www.w3.org/2005/Atom'}
 for e in root.findall('a:entry',ns):
  print(e.findtext('a:id',namespaces=ns),e.findtext('a:title',namespaces=ns),e.findtext('a:summary',namespaces=ns))
 assert sha(p)==a
if sys.argv[1]=='admin':
 root=B.parents[3]
 p=root/'AGENTS.md'
 records=json.loads((L/'freeze.json').read_text());records.append(freeze(p,L/'administrative/ancestor-AGENTS.md'))
 (L/'freeze.json').write_text(json.dumps(records,indent=2))
 for name in ['ledger.json','prior-campaign-context.json']:
  obj=json.loads((L/'administrative'/name).read_text());print(name,'keys',list(obj))
  if name=='ledger.json':print('counts',{k:obj[k] for k in ['accepted_count','total_accepted_count','next_global_outcome_number']})
if sys.argv[1]=='extract':
 p=L/'sources'/sys.argv[2];a=sha(p);o=p.with_suffix('.txt')
 subprocess.run(['pdftotext','-layout',str(p),str(o)],check=True)
 assert sha(p)==a
 (o.with_suffix('.txt.sha256')).write_text(sha(o)+'\n')
 print(o,sha(o))
if sys.argv[1]=='history':
 p=L.parent/'sol-trip-breadth-depth-r1/history-bindings.json'; bound=freeze(p,L/'history-bindings.json');refs=json.loads(p.read_text());hits=[];bad=[]
 terms=['1905.06692','antichain generating','connected peck','ding and dong','genius conjecture','1501.04540','peckness of edge','1506.04406','mobius function of the permutation','common cover transitive','hemminger','2411.12034','tangled labelings','federbush']
 for r in refs:
  q=pathlib.Path(r['path'])
  if not q.exists() or sha(q)!=r['sha256']:bad.append(str(q));continue
  s=q.read_text(errors='replace').lower();found=[t for t in terms if t in s]
  if found:hits.append(dict(path=str(q),terms=found,lines=[x for x in s.splitlines() if any(t in x for t in found)][:12]))
  assert sha(q)==r['sha256']
 report=dict(binding=bound,references=len(refs),bad=bad,hits=hits,terms=terms)
 (L/'history-screen.json').write_text(json.dumps(report,indent=2));print(json.dumps(report,indent=2))
