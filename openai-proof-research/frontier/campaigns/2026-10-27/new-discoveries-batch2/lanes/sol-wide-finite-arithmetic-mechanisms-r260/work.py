from pathlib import Path
import urllib.request,urllib.parse,json,hashlib,datetime,sys,subprocess,xml.etree.ElementTree as E
L=Path(__file__).resolve().parent
S=L/'frozen'; S.mkdir(exist_ok=True)
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def fetch(url,name):
 p=S/name
 if p.exists():return p
 r={'url':url,'utc':datetime.datetime.now(datetime.timezone.utc).isoformat()}
 try:
  with urllib.request.urlopen(urllib.request.Request(url,headers={'User-Agent':'MathResearch/1.0'}),timeout=25) as z:
   data=z.read(10000000);r.update(status=z.status,final_url=z.url)
  p.write_bytes(data);r.update(path=str(p),bytes=len(data),sha256=sha(p))
 except Exception as e:r['failure']=repr(e)
 with (L/'retrieval.jsonl').open('a') as f:f.write(json.dumps(r)+'\n')
 return p if p.exists() else None
def body(id):
 p=fetch('https://arxiv.org/pdf/'+id,id+'.pdf')
 if p:
  h=sha(p); t=S/(id+'.txt');subprocess.run(['pdftotext','-layout',str(p),str(t)],check=True)
  assert sha(p)==h
  with (L/'bindings.jsonl').open('a') as f:f.write(json.dumps({'original':str(p),'sha256':h,'text':str(t),'text_sha256':sha(t)})+'\n')
  return t
if __name__=='__main__':
 if sys.argv[1]=='query':
  q=sys.argv[2];p=fetch('https://export.arxiv.org/api/query?'+urllib.parse.urlencode({'search_query':q,'start':0,'max_results':60,'sortBy':'submittedDate','sortOrder':'ascending'}),sys.argv[3]+'.xml')
  if p:
   ns={'a':'http://www.w3.org/2005/Atom'};out=[]
   for e in E.fromstring(p.read_bytes()).findall('a:entry',ns):
    out.append({k:e.findtext('a:'+k,default='',namespaces=ns).strip().replace('\n',' ') for k in ['id','title','summary','published','updated']})
   (L/(sys.argv[3]+'.json')).write_text(json.dumps(out,indent=2));print("\n".join(x["id"]+" "+x["title"]+" "+x["summary"][:700] for x in out))
 elif sys.argv[1]=='body':
  for id in sys.argv[2:]:
   t=body(id)
   if t:
    lines=t.read_text().splitlines();hits=[i for i,x in enumerate(lines) if any(z in x.lower() for z in ['conjecture','open question','open problem','we ask'])];print('BODY',id,len(lines))
    for i in hits[-16:]:print('\n'.join(lines[max(0,i-2):i+6]))
