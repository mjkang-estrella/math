from pathlib import Path
import sys,json,hashlib,urllib.request,urllib.parse,datetime,subprocess,re
L=Path(__file__).resolve().parent; B=L.parent.parent
def h(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def get(url,name):
 p=L/'primary'/name;q=L/'frozen-sources'/name;p.parent.mkdir(exist_ok=True);q.parent.mkdir(exist_ok=True)
 try:
  with urllib.request.urlopen(urllib.request.Request(url,headers={'User-Agent':'Research source audit contact local'}),timeout=35) as r:
   data=r.read(12000000); status=r.status
  p.write_bytes(data);s=h(p);q.write_bytes(data);assert h(q)==h(p)==s
  with (L/'sources.jsonl').open('a') as f:f.write(json.dumps(dict(url=url,original=str(p),copy=str(q),sha256=s,time=datetime.datetime.now(datetime.timezone.utc).isoformat(),status=status))+'\n')
  return q
 except Exception as e:
  with (L/'failures.jsonl').open('a') as f:f.write(json.dumps(dict(url=url,error=str(e),time=datetime.datetime.now(datetime.timezone.utc).isoformat()))+'\n')
  print('FAILED',url,str(e));return None
mode=sys.argv[1]
if mode=='url':
 p=get(sys.argv[2],sys.argv[3]);print(str(p))
elif mode=='metadata':
 p=get('https://export.arxiv.org/api/query?'+urllib.parse.urlencode(dict(id_list=','.join(sys.argv[2:]))),'chronology.xml')
 if p:
  import xml.etree.ElementTree as E
  ns='{http://www.w3.org/2005/Atom}'; out=[]
  for e in E.fromstring(p.read_bytes()).findall(ns+'entry'):
   out.append({k:e.findtext(ns+k) for k in ('id','title','published','updated')})
  (L/'chronology.json').write_text(json.dumps(out,indent=2));print(json.dumps(out,indent=2))
elif mode=='search':
 import xml.etree.ElementTree as E
 for i,query in enumerate(sys.argv[2:]):
  p=get('https://export.arxiv.org/api/query?'+urllib.parse.urlencode(dict(search_query=query,start=0,max_results=20,sortBy='submittedDate',sortOrder='descending')),'search-'+hashlib.sha256(query.encode()).hexdigest()[:12]+'.xml')
  if p:
   for e in E.fromstring(p.read_bytes()).findall('{http://www.w3.org/2005/Atom}entry'):
    print(e.findtext('{http://www.w3.org/2005/Atom}id'),e.findtext('{http://www.w3.org/2005/Atom}title'),e.findtext('{http://www.w3.org/2005/Atom}summary')[:1100])
elif mode=='pdf':
 for id in sys.argv[2:]:
  p=get('https://arxiv.org/pdf/'+id,id+'.pdf')
  if p:
   s=h(p);t=L/'texts'/(id+'.txt');t.parent.mkdir(exist_ok=True)
   subprocess.run(['pdftotext','-layout',str(p),str(t)],check=True);assert h(p)==s==h(L/'primary'/p.name)
   lines=t.read_text().splitlines()
   print('\nSOURCE',id)
   for i,line in enumerate(lines):
    if re.search('conjectur|open question|problem [0-9]',line,re.I):print(i+1,'\n'.join(lines[max(0,i-2):i+12]))
elif mode=='history':
 patterns=sys.argv[2:];found=[]
 for p in B.joinpath('lanes').glob('*/*'):
  if p.name not in ('SCOUTING.md','SUMMARY.md','discovery.md','PROOF.md','STATUS.md'):continue
  if p.stat().st_size>300000:continue
  data=p.read_text(errors='replace')
  hits=[x for x in patterns if re.search(x,data,re.I)]
  if hits:found.append(dict(path=str(p),sha256=h(p),hits=hits,lines=[a[:500] for a in data.splitlines() if any(re.search(x,a,re.I) for x in hits)][:12]))
 (L/'history-hits.json').write_text(json.dumps(found,indent=2));print(json.dumps(found,indent=2))
