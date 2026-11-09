import pathlib,json,urllib.request,hashlib,datetime,subprocess
from html.parser import HTMLParser
P=pathlib.Path(__file__).resolve().parent;log=json.loads((P/'source-provenance.json').read_text())
class Parser(HTMLParser):
 def handle_starttag(self,t,a):
  d=dict(a)
  if t=='meta' and d.get('name')=='citation_pdf_url':self.url=d['content']
for id in [1532,1537,1587,1593]:
 h=Parser();h.feed((P/f'ems{id}.html').read_text());url=h.url;name=f'ems{id}.pdf'
 try:
  with urllib.request.urlopen(urllib.request.Request(url,headers={'User-Agent':'ResearchReader/1.0'}),timeout=25) as r:b=r.read();final=r.url
  (P/name).write_bytes(b);log.append(dict(url=url,final_url=final,path=name,size=len(b),sha256=hashlib.sha256(b).hexdigest(),utc=datetime.datetime.now(datetime.timezone.utc).isoformat(),status='bound_before_extraction'));(P/'source-provenance.json').write_text(json.dumps(log,indent=2)+'\n')
  subprocess.run(['pdftotext','-layout',str(P/name),str(P/f'ems{id}.txt')],check=True)
  t=P/f'ems{id}.txt';b=t.read_bytes();log.append(dict(path=t.name,size=len(b),sha256=hashlib.sha256(b).hexdigest(),derived_from=name,utc=datetime.datetime.now(datetime.timezone.utc).isoformat(),status='bound_before_reading'));(P/'source-provenance.json').write_text(json.dumps(log,indent=2)+'\n');print(id,'bound')
 except Exception as e:
  log.append(dict(url=url,error=str(e),retry=False));(P/'source-provenance.json').write_text(json.dumps(log,indent=2)+'\n');print(e)
