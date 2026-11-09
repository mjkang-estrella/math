import pathlib,json,hashlib,urllib.request,datetime,subprocess
from html.parser import HTMLParser
P=pathlib.Path(__file__).resolve().parent
class Parser(HTMLParser):
 def handle_starttag(self,t,a):
  d=dict(a)
  if t=='meta' and d.get('name')=='citation_pdf_url':self.url=d['content']
def ent(p):
 b=p.read_bytes();return dict(path=p.name,size=len(b),sha256=hashlib.sha256(b).hexdigest())
out=[];der=[]
for e in json.loads((P/'fetch-provenance.json').read_text()):
 p=P/e['path'];assert ent(p)['sha256']==e['sha256'];parser=Parser();parser.feed(p.read_text());url=parser.url
 try:
  with urllib.request.urlopen(urllib.request.Request(url,headers={'User-Agent':'Mozilla/5.0','Accept':'application/pdf'}),timeout=25) as r:b=r.read();final=r.url
  pdf=p.with_suffix('.pdf');pdf.write_bytes(b);a=ent(pdf);a.update(url=url,final_url=final,utc=datetime.datetime.now(datetime.timezone.utc).isoformat());out.append(a)
  (P/'pdf-bindings.json').write_text(json.dumps(out,indent=2)+'\n')
  assert b.startswith(b'%PDF');assert ent(pdf)['sha256']==a['sha256']
  txt=pdf.with_suffix('.txt');subprocess.run(['pdftotext','-layout',str(pdf),str(txt)],check=True);der.append(ent(txt));(P/'derivative-bindings.json').write_text(json.dumps(der,indent=2)+'\n')
 except Exception as ex:out.append(dict(url=url,error=str(ex)));(P/'pdf-bindings.json').write_text(json.dumps(out,indent=2)+'\n')
print(json.dumps(out))
