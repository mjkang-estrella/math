from pathlib import Path
import hashlib,json,sys,datetime,urllib.request,subprocess
L=Path(__file__).resolve().parent
B=L.parent.parent
def sha(p): return hashlib.sha256(p.read_bytes()).hexdigest()
def write(p,x):
 p.parent.mkdir(parents=True,exist_ok=True);p.write_text(x if isinstance(x,str) else json.dumps(x,indent=2))
def freeze(paths):
 f=L/'references.json'; rows=json.loads(f.read_text()) if f.exists() else []
 for p in paths:
  if not p.is_file() or any(r['path']==str(p) for r in rows):continue
  rows.append({'path':str(p),'sha256':sha(p),'bytes':p.stat().st_size,'frozen_utc':datetime.datetime.now(datetime.timezone.utc).isoformat()})
 write(f,rows)
def verify():
 for r in json.loads((L/'references.json').read_text()):assert sha(Path(r['path']))==r['sha256'],r['path']
if sys.argv[1]=='init':
 for n in ['AGENTS.md','ledger.json','prior-campaign-context.json']:
  write(L/'administrative'/n,(B/n).read_text())
 write(L/'administrative'/'ancestor-AGENTS.md',(B.parents[3]/'AGENTS.md').read_text())
 paths=[]
 for name in ['sol-wide-new-mechanism-scout-r220','sol-trip-breadth-depth-r1']:
  D=L.parent/name
  paths.extend(D/n for n in ['SCOUTING.md','SUMMARY.md','PROOF.md','provenance.json','freeze.json'])
  if name.endswith('r220'):paths.extend((D/'sources').glob('*'))
 freeze(paths);verify()
 print('frozen',len(json.loads((L/'references.json').read_text())))
 print('ledger counts', {k:json.loads((L/'administrative'/'ledger.json').read_text())[k] for k in ['accepted_count','total_accepted_count','next_global_outcome_number']})
elif sys.argv[1]=='read':
 verify()
 for name in sys.argv[2:]:
  p=Path(name); print('\nFILE',p);print(p.read_text()[:42000])
 verify()
elif sys.argv[1]=='get':
 url,name=sys.argv[2:];p=L/'sources'/name
 try:
  req=urllib.request.Request(url,headers={'User-Agent':'Mathematical source research (bounded request)'})
  with urllib.request.urlopen(req,timeout=35) as r:
   data=r.read(12000000);status=r.status
  p.parent.mkdir(exist_ok=True);p.write_bytes(data);freeze([p]);out={'url':url,'status':status,'path':str(p),'sha256':sha(p)}
 except Exception as e:out={'url':url,'error':str(e)}
 with (L/'access.jsonl').open('a') as f:f.write(json.dumps(out)+'\n')
 print(out)
elif sys.argv[1]=='excerpt':
 verify();p=Path(sys.argv[2]);s=p.read_text();lines=s.splitlines()
 for i,line in enumerate(lines):
  if any(w.lower() in line.lower() for w in sys.argv[3:]):print('\n'.join(f'{j+1}: {lines[j]}' for j in range(max(0,i-5),min(len(lines),i+12))))
 verify()
elif sys.argv[1]=='links':
 import re,html
 verify();s=Path(sys.argv[2]).read_text()
 for url,t in re.findall(r'<a[^>]*href="([^"]+)"[^>]*>(.*?)</a>',s,re.S):
  t=html.unescape(re.sub('<[^>]*>',' ',t))
  if any(w.lower() in (t+' '+url).lower() for w in sys.argv[3:]):print(url,t[:400])
 verify()
elif sys.argv[1]=='extract':
 verify()
 for n in sys.argv[2:]:
  p=L/'sources'/n;t=p.with_suffix('.txt');subprocess.run(['pdftotext','-layout',str(p),str(t)],check=True);freeze([t])
 verify()
elif sys.argv[1]=='breadth':
 import xml.etree.ElementTree as ET
 verify();root=ET.parse(L/'sources'/'breadth.xml').getroot();ns={'a':'http://www.w3.org/2005/Atom'}
 for e in root.findall('a:entry',ns):
  ident=e.find('a:id',ns).text.split('/')[-1];p=L/'sources'/(ident+'.pdf');t=p.with_suffix('.txt');url='https://arxiv.org/pdf/'+ident
  try:
   with urllib.request.urlopen(url,timeout=20) as r:data=r.read(10000000)
   p.write_bytes(data);freeze([p]);subprocess.run(['pdftotext','-layout',str(p),str(t)],check=True);freeze([t]);out={'url':url,'status':200,'sha256':sha(p),'time':datetime.datetime.now(datetime.timezone.utc).isoformat()}
  except Exception as ex:out={'url':url,'error':str(ex)}
  with (L/'access.jsonl').open('a') as f:f.write(json.dumps(out)+'\n')
  print(out,flush=True)
 verify()
elif sys.argv[1]=='body-screen':
 verify()
 for p in sorted((L/'sources').glob('2610*.txt')):
  s=p.read_text();lines=s.splitlines();print('\nFILE',p.name,'pages',s.count('\f')+1)
  ids=set(range(min(90,len(lines))))
  for i,line in enumerate(lines):
   if any(w in line.lower() for w in ['conjecture','question','problem 6','problem 7','future work']):ids.update(range(max(0,i-2),min(len(lines),i+12)))
  print('\n'.join(f'{i+1}: {lines[i]}' for i in sorted(ids))[:21000])
 verify()
elif sys.argv[1]=='pages':
 verify();p=L/'sources'/sys.argv[2];pages=p.read_text().split('\f')
 for n in sys.argv[3:]:print('\nPAGE',n,'\n',pages[int(n)-1])
 verify()
elif sys.argv[1]=='compact':
 verify()
 for p in sorted((L/'sources').glob('2610*.txt')):
  print('\nFILE',p.name)
  lines=p.read_text().splitlines();hits=0
  for i,line in enumerate(lines):
   if line.strip().startswith(('Theorem 1.','Conjecture 1.','Question 1.','Theorem A','Conjecture A','Theorem 2.','Conjecture 2.')):
    print('\n'.join(lines[max(0,i-1):i+9]));hits+=1
    if hits>=5:break
 verify()
elif sys.argv[1]=='history':
 paths=[]
 for D in L.parent.iterdir():
  if any(D.name.endswith('r'+str(n)) for n in range(213,222)):
   paths.extend(p for p in D.iterdir() if p.name in ['SCOUTING.md','SUMMARY.md','discovery.md'])
 freeze(paths);verify();terms=['2610.40321','2610.39630','2610.39481','symbolic depth','non-transitive dice','e-positive tree','2610.39051','Fasi']
 out=[]
 for p in paths:
  for i,line in enumerate(p.read_text().splitlines()):
   if any(t.lower() in line.lower() for t in terms):out.append({'path':str(p),'line':i+1,'text':line})
 write(L/'history-screen.json',{'references':len(paths),'terms':terms,'hits':out});print(json.dumps(out,indent=2))
 verify()
