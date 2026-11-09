from pathlib import Path
import urllib.request,urllib.error,hashlib,json,datetime,sys,subprocess
L=Path(__file__).resolve().parent
def get(url,name):
 p=L/'sources'/name;p.parent.mkdir(exist_ok=True)
 if p.exists():return p
 row={'url':url,'utc':datetime.datetime.now(datetime.timezone.utc).isoformat()}
 try:
  with urllib.request.urlopen(urllib.request.Request(url,headers={'User-Agent':'Research source verification'}),timeout=35) as r:data=r.read(12000000);row['status']=r.status
  p.write_bytes(data);row.update(sha256=hashlib.sha256(data).hexdigest(),bytes=len(data),path=str(p))
 except Exception as e:row['error']=str(e)
 with (L/'http.jsonl').open('a') as f:f.write(json.dumps(row)+'\n')
 print(json.dumps(row))
 return p if p.exists() else None
if __name__=='__main__':
 if sys.argv[1]=='search':
  import urllib.parse
  for i,q in enumerate(sys.argv[2:]):
   p=get('https://export.arxiv.org/api/query?search_query='+urllib.parse.quote(q)+'&start=0&max_results=12&sortBy=submittedDate&sortOrder=descending','search'+str(i)+'.xml')
   if p:
    import xml.etree.ElementTree as E
    t=E.fromstring(p.read_bytes());ns={'a':'http://www.w3.org/2005/Atom'}
    for e in t.findall('a:entry',ns):print(e.find('a:id',ns).text,e.find('a:title',ns).text,e.find('a:summary',ns).text[:1600])
 if sys.argv[1]=='pdf':
  for ident in sys.argv[2:]:
   p=get('https://arxiv.org/pdf/'+ident,ident+'.pdf')
   if p:
    h=hashlib.sha256(p.read_bytes()).hexdigest();subprocess.run(['pdftotext','-layout',str(p),str(p.with_suffix('.txt'))],check=True);assert hashlib.sha256(p.read_bytes()).hexdigest()==h
    print(p.with_suffix('.txt').read_text()[:1200])
