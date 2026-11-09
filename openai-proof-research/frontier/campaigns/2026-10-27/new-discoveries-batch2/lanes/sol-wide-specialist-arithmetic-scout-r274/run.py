import pathlib,hashlib,json,sys,shutil,urllib.request,datetime,subprocess
L=pathlib.Path(__file__).resolve().parent
B=L.parent.parent
def sha(p): return hashlib.sha256(p.read_bytes()).hexdigest()
def dump(p,x): p.write_text(json.dumps(x,indent=2)+'\n')
if sys.argv[1]=='init':
 (L/'admin').mkdir(exist_ok=True); (L/'sources').mkdir(exist_ok=True)
 for n in ['AGENTS.md','ledger.json','prior-campaign-context.json']: shutil.copyfile(B/n,L/'admin'/n)
 paths=[B/'lanes/sol-wide-finite-arithmetic-source-r272/SCOUTING.md', B/'lanes/root-scout-r272-disposition/STATUS.md', B/'lanes/root-scout-r272-disposition/SCOUTING.md']
 dump(L/'bindings.json',[{'path':str(p),'sha256':sha(p),'size':p.stat().st_size,'mode':'immutable external reference; verified before scientific read'} for p in paths])
 for p in paths: print('\nSOURCE',p,'\n',p.read_text())
 for n in ['ledger.json','prior-campaign-context.json']:
  d=json.loads((L/'admin'/n).read_text()); print(n,[(x.get('number'),x.get('title')) for x in d.get('accepted',[])])
elif sys.argv[1]=='fetch':
 name,url=sys.argv[2:4]; p=L/'sources'/name
 record={'url':url,'at':datetime.datetime.now(datetime.timezone.utc).isoformat(),'path':str(p)}
 try:
  with urllib.request.urlopen(urllib.request.Request(url,headers={'User-Agent':'Mathematical research source reader'}),timeout=25) as r:
   data=r.read(10000001);record.update(status=r.status,final_url=r.url)
  if len(data)>10000000: raise ValueError('10MB bound')
  p.write_bytes(data); record.update(sha256=sha(p),size=len(data),frozen_before_read=True)
 except Exception as e: record['error']=str(e)
 with (L/'access.jsonl').open('a') as f: f.write(json.dumps(record)+'\n')
 print(json.dumps(record))
elif sys.argv[1]=='extract':
 p=L/'sources'/sys.argv[2];before=sha(p)
 subprocess.run(['pdftotext','-layout',str(p),str(p.with_suffix('.txt'))],check=True)
 assert before==sha(p)
 with (L/'derived.jsonl').open('a') as f:f.write(json.dumps({'original':str(p),'sha256':before,'text':str(p.with_suffix('.txt')),'text_sha256':sha(p.with_suffix('.txt'))})+'\n')
elif sys.argv[1]=='history':
 needles=['canonical reduction','2003.05391','2609.04000','2406.00790','2608.19984','nearly Gorenstein','weak Wilf']
 rows=[]
 for p in sorted((B/'lanes').glob('*/SCOUTING.md')):
  if p.parent==L or p.stat().st_size>150000:continue
  h=sha(p);t=p.read_text();hits=[n for n in needles if n.lower() in t.lower()]; assert h==sha(p)
  rows.append({'path':str(p),'sha256':h,'hits':hits})
 dump(L/'history.json',rows);print(json.dumps([r for r in rows if r['hits']],indent=2))
elif sys.argv[1]=='range':
 p=L/'sources'/sys.argv[2];h=sha(p);lines=p.read_text().splitlines();a,b=map(int,sys.argv[3:5]);print('\n'.join(f'{i+1}: {lines[i]}' for i in range(a-1,min(b,len(lines)))));assert sha(p)==h
elif sys.argv[1]=='feed':
 import xml.etree.ElementTree as ET
 for n in sys.argv[2:]:
  p=L/'sources'/n;before=sha(p);root=ET.fromstring(p.read_bytes());ns={'a':'http://www.w3.org/2005/Atom'}
  for e in root.findall('a:entry',ns):
   print(e.findtext('a:id',namespaces=ns),e.findtext('a:title',namespaces=ns),e.findtext('a:updated',namespaces=ns)); print(e.findtext('a:summary',namespaces=ns))
  assert sha(p)==before
elif sys.argv[1]=='read':
 p=L/'sources'/sys.argv[2]; before=sha(p); t=p.read_text(); needles=sys.argv[3:] or ['open problem','conjecture','question','concluding']
 lines=t.splitlines();seen=set()
 for i,line in enumerate(lines):
  if any(n.lower() in line.lower() for n in needles):
   for j in range(max(0,i-4),min(len(lines),i+22)):
    if j not in seen:print(f'{j+1}: {lines[j]}');seen.add(j)
 assert sha(p)==before
