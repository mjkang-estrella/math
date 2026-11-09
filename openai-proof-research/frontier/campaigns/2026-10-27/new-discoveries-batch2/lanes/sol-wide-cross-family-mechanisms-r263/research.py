import pathlib,json,hashlib,urllib.request,datetime,xml.etree.ElementTree as E,subprocess,sys
L=pathlib.Path(__file__).parent;B=L.parent.parent
def h(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def fetch(url,p):
 try:
  with urllib.request.urlopen(urllib.request.Request(url,headers={'User-Agent':'MathematicsResearch/1.0'}),timeout=28) as r:data=r.read(12000000)
  p.parent.mkdir(exist_ok=True);p.write_bytes(data);rec=dict(url=url,path=str(p),sha256=h(p),utc=str(datetime.datetime.now(datetime.timezone.utc)),bytes=len(data),status='OK')
 except Exception as e:rec=dict(url=url,error=str(e),status='FAIL',utc=str(datetime.datetime.now(datetime.timezone.utc)))
 with (L/'retrieval.jsonl').open('a') as f:f.write(json.dumps(rec)+'\n')
 return rec['status']=='OK'
def query(q,name):
 p=L/(name+'.xml')
 if not fetch('https://export.arxiv.org/api/query?search_query='+urllib.parse.quote(q)+'&max_results=100&sortBy=submittedDate&sortOrder=ascending',p):print('FAIL');return
 ns={'a':'http://www.w3.org/2005/Atom'};out=[]
 for e in E.parse(p).findall('a:entry',ns):
  d={k:e.findtext('a:'+k,namespaces=ns) for k in ['id','title','summary','published','updated']};d['authors']=[a.findtext('a:name',namespaces=ns) for a in e.findall('a:author',ns)];out.append(d)
 (L/(name+'.json')).write_text(json.dumps(out,indent=2))
 for i,d in enumerate(out):print(i,d['id'],d['authors'],d['title'],d['summary'][:950])
if __name__=='__main__':query(sys.argv[1],sys.argv[2])
