import pathlib,json,hashlib,urllib.request,datetime,subprocess
from html.parser import HTMLParser
P=pathlib.Path(__file__).resolve().parent;log=json.loads((P/'source-provenance.json').read_text())
class Meta(HTMLParser):
 def handle_starttag(self,t,a):
  d=dict(a)
  if t=='meta' and d.get('name')=='citation_pdf_url':self.url=d['content']
def save(): (P/'source-provenance.json').write_text(json.dumps(log,indent=2)+'\n')
for id in [3388,2053,2091]:
 m=Meta();m.feed((P/f'ems{id}.html').read_text());u=m.url;p=P/f'ems{id}.pdf'
 try:
  with urllib.request.urlopen(urllib.request.Request(u,headers={'User-Agent':'Python-urllib/3'}),timeout=25) as r:b=r.read();final=r.url
  assert b.startswith(b'%PDF');p.write_bytes(b);log.append({'url':u,'final_url':final,'utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'path':p.name,'sha256':hashlib.sha256(b).hexdigest(),'size':len(b),'kind':'primary report PDF'});save()
  t=p.with_suffix('.txt');subprocess.run(['pdftotext','-layout',str(p),str(t)],check=True);b=t.read_bytes();log.append({'path':t.name,'sha256':hashlib.sha256(b).hexdigest(),'size':len(b),'derived_from':p.name,'command':'pdftotext -layout','utc':datetime.datetime.now(datetime.timezone.utc).isoformat()});save()
  terms={3388:['Non-Integrality','fully Hilbertian','period-index'],2053:['strong Tits','Strong Tits'],2091:['supercongruence','(4n','Van Hamme','van Hamme']}[id]
  lines=b.decode().splitlines();out=[]
  for n,line in enumerate(lines):
   if any(s.lower() in line.lower() for s in terms):
    lo=max(0,n-8);hi=min(len(lines),n+23);out.append({'start_line':lo+1,'end_line':hi,'text':'\n'.join(lines[lo:hi])})
  q=P/f'ems{id}-passages.json';q.write_text(json.dumps(out,ensure_ascii=False,indent=2)+'\n');print('REPORT',id,json.dumps(out,ensure_ascii=False))
 except Exception as e:log.append({'url':u,'error':str(e),'stopped':True});save();print('ERROR',id,e)
