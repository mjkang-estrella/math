import pathlib,json,hashlib,urllib.request,datetime,xml.etree.ElementTree as E,subprocess
L=pathlib.Path(__file__).parent;B=L.parent.parent
def digest(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def fetch(url,p):
 try:
  with urllib.request.urlopen(urllib.request.Request(url,headers={'User-Agent':'MathematicsResearch/1.0'}),timeout=35) as r:
   data=r.read(16000000)
  p.write_bytes(data)
  rec=dict(url=url,path=str(p),sha256=digest(p),utc=str(datetime.datetime.now(datetime.timezone.utc)),bytes=len(data),status='OK')
 except Exception as e:rec=dict(url=url,error=str(e),status='FAIL',utc=str(datetime.datetime.now(datetime.timezone.utc)))
 with (L/'retrieval.jsonl').open('a') as f:f.write(json.dumps(rec)+'\n')
 print(json.dumps(rec));return rec['status']=='OK'
if __name__=='__main__':
 url='https://export.arxiv.org/api/query?search_query=submittedDate:[201904010000+TO+201904302359]+AND+(cat:math.CO+OR+cat:math.NT+OR+cat:math.RA)&start=0&max_results=100&sortBy=submittedDate&sortOrder=ascending'
 p=L/'slice.xml'
 if fetch(url,p):
  ns={'a':'http://www.w3.org/2005/Atom'};out=[]
  for e in E.parse(p).findall('a:entry',ns):
   d={k:e.findtext('a:'+k,namespaces=ns) for k in ['id','title','summary','published','updated']};d['authors']=[a.findtext('a:name',namespaces=ns) for a in e.findall('a:author',ns)];out.append(d)
  (L/'slice.json').write_text(json.dumps(out,indent=2))
  for i,d in enumerate(out):print(i,d['id'],d['title'],d['summary'][:650])
