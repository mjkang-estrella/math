import urllib.request,urllib.error,json,pathlib,hashlib,datetime,html.parser
O=pathlib.Path(__file__).parent
pro=[];fail=[]
class Text(html.parser.HTMLParser):
 def __init__(self):super().__init__();self.parts=[];self.skip=0
 def handle_starttag(self,t,a):
  if t in ('script','style'):self.skip+=1
  if t in ('p','div','section','h1','h2','h3','h4','li'):self.parts.append('\n')
 def handle_endtag(self,t):
  if t in ('script','style'):self.skip=max(0,self.skip-1)
 def handle_data(self,d):
  if not self.skip:self.parts.append(d)
def binding(p):return {'path':str(p.resolve()),'sha256':hashlib.sha256(p.read_bytes()).hexdigest(),'size':p.stat().st_size}
for a in ['2604.21187','2604.02475','2603.02698','2510.23200','2601.06208']:
 url='https://arxiv.org/html/'+a+'v1';now=datetime.datetime.now(datetime.timezone.utc).isoformat()
 try:
  with urllib.request.urlopen(urllib.request.Request(url,headers={'User-Agent':'Mozilla/5.0','Accept':'text/html'}),timeout=25) as r:b=r.read();final=r.url
  p=O/(a+'v1.html');p.write_bytes(b);entry={'url':url,'final_url':final,'utc':now,'version':'v1','original':binding(p)}
  # bind bytes before parsing, and derivative before reading
  pro.append(entry);(O/'source-provenance.json').write_text(json.dumps(pro,indent=2)+'\n')
  parser=Text();parser.feed(b.decode());q=O/(a+'v1.txt');q.write_text(''.join(parser.parts));entry['derivative']=binding(q)
  (O/'source-provenance.json').write_text(json.dumps(pro,indent=2)+'\n');print(a,'OK',len(b),q.stat().st_size)
 except Exception as e:
  fail.append({'url':url,'utc':now,'error':str(e),'retry':False});print(a,str(e))
(O/'fetch-failures.json').write_text(json.dumps(fail,indent=2)+'\n')
