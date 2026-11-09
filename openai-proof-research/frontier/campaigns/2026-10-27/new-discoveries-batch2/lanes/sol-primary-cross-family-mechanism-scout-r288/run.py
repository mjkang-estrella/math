import pathlib, json, hashlib, shutil, urllib.request, time, sys, subprocess
L=pathlib.Path(__file__).resolve().parent
B=L.parent.parent
def sha(p): return hashlib.sha256(p.read_bytes()).hexdigest()
def save(p,b):
 p.parent.mkdir(parents=True,exist_ok=True);p.write_bytes(b)
def dump(p,o): save(p,(json.dumps(o,indent=2,ensure_ascii=False)+'\n').encode())
if sys.argv[1]=='init':
 records=[]
 for p in [B/'ledger.json', B/'prior-campaign-context.json',B/'AGENTS.md',B.parent.parent.parent.parent/'AGENTS.md',B/'lanes/sol-csordas-forgacs-czds-preliminary-review-r1/SCOUTING.md']:
  if not p.exists(): continue
  h=sha(p);q=L/'administrative'/p.name
  if q.exists():q=L/'administrative'/('ancestor-'+p.name)
  save(q,p.read_bytes());records.append(dict(original=str(p),snapshot=str(q.relative_to(L)),before=h,after=sha(p),copy=sha(q)))
 dump(L/'administrative-bindings.json',records)
 for n in ['ledger.json','prior-campaign-context.json']:
  x=json.loads((B/n).read_text()); print(n, json.dumps({k:v for k,v in x.items() if k not in ['accepted','first_batch_published_results']})[:5000]);print('ACCEPTED',[(r.get('number'),r.get('title')) for r in x.get('accepted',[])])
elif sys.argv[1] in ['search','older']:
 failures=[]
 for cat in (['CO','RA','NT','CA'] if sys.argv[1]=='search' else ['CO','NT','CA']):
  old=sys.argv[1]=='older'
  u='https://export.arxiv.org/api/query?search_query=cat:math.'+cat+'+AND+all:conjecture&start=0&max_results='+('1' if old else '4')+'&sortBy=submittedDate&sortOrder='+('ascending' if old else 'descending')
  try:
   with urllib.request.urlopen(u,timeout=25) as r:b=r.read(2000000);status=r.status
   p=L/'search'/(('older-' if old else 'math-')+cat+'.xml');save(p,b);dump(p.with_suffix('.binding.json'),dict(url=u,status=status,sha256=sha(p),retrieved=time.strftime('%Y-%m-%dT%H:%M:%SZ',time.gmtime())));print(cat,status,len(b))
  except Exception as e: failures.append(dict(url=u,error=str(e)));print(cat,str(e))
 dump(L/('search-failures-'+sys.argv[1]+'.json'),failures)
elif sys.argv[1]=='bodies':
 import xml.etree.ElementTree as ET
 rows=json.loads((L/'primary-bindings.json').read_text()) if (L/'primary-bindings.json').exists() else [];ns={'a':'http://www.w3.org/2005/Atom'}
 for p in sorted((L/'search').glob('*.xml')):
  for e in ET.fromstring(p.read_bytes()).findall('a:entry',ns):
   aid=e.find('a:id',ns).text.split('/abs/')[-1];title=' '.join(e.find('a:title',ns).text.split())
   if any(r['id']==aid for r in rows):continue
   row=dict(id=aid,title=title,category=p.stem,authors=[a.find('a:name',ns).text for a in e.findall('a:author',ns)],published=e.find('a:published',ns).text,updated=e.find('a:updated',ns).text)
   u='https://arxiv.org/pdf/'+aid;row['url']=u
   try:
    with urllib.request.urlopen(u,timeout=20) as r:b=r.read(12000000);row['status']=r.status
    q=L/'primary'/ (aid.replace('/','_')+'.pdf');save(q,b);row['sha256']=sha(q);row['bytes']=len(b);row['retrieved']=time.strftime('%Y-%m-%dT%H:%M:%SZ',time.gmtime())
    f=L/'frozen'/q.name;save(f,b);row['frozen_sha256']=sha(f);f.chmod(0o444)
    # Freeze bytes before any parser/scientific reading; the saved original is never modified.
    q.chmod(0o444)
    if not b.startswith(b'%PDF'):raise ValueError('non-PDF response')
    t=L/'texts'/(aid.replace('/','_')+'.txt');t.parent.mkdir(exist_ok=True)
    subprocess.run(['pdftotext','-layout',str(q),str(t)],check=True,timeout=15)
    row['after_sha256']=sha(q);row['text_sha256']=sha(t)
   except Exception as ex:row['error']=str(ex)
   rows.append(row);dump(L/'primary-bindings.json',rows);print(json.dumps(row),flush=True)
elif sys.argv[1] in ['inventory','compact']:
 for r in json.loads((L/'primary-bindings.json').read_text()):
  print('\n###',r['id'],r['title'],r['authors'],r['published'],r['updated'])
  p=L/'texts'/(r['id'].replace('/','_')+'.txt')
  if p.exists():
   lines=p.read_text().splitlines()
   import re
   hits=[i for i,s in enumerate(lines) if re.search(r'conjectur|open problem|question|theorem 1|problem [0-9]',s,re.I)]
   if sys.argv[1]=='compact':
    hits=[i for i,s in enumerate(lines) if re.search(r'^(Conjecture|Question|Problem|Theorem [1A-C])',s.strip())][:6]
   for i in hits[:22]: print(str(i+1)+': '+' '.join(lines[max(0,i-1):i+7]))
