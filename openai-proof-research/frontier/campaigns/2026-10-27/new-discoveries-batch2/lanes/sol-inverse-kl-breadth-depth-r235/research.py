from pathlib import Path
import urllib.request,urllib.error,hashlib,json,datetime,subprocess,sys
L=Path(__file__).resolve().parent
def digest(p): return hashlib.sha256(p.read_bytes()).hexdigest()
def fetch(name,url):
 p=L/'primary'/name;p.parent.mkdir(exist_ok=True)
 rec={'url':url,'utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'name':name}
 try:
  with urllib.request.urlopen(urllib.request.Request(url,headers={'User-Agent':'MathematicalResearch/1.0'}),timeout=25) as r:
   data=r.read(12000000);rec.update(status=r.status,final_url=r.url)
  p.write_bytes(data);rec['sha256']=digest(p);rec['size']=len(data)
  p.chmod(0o444)
  if data.startswith(b'%PDF'):
   subprocess.run(['pdftotext','-layout',str(p),str(p.with_suffix('.txt'))],check=True)
   p.with_suffix('.txt').chmod(0o444);rec['text_sha256']=digest(p.with_suffix('.txt'))
 except Exception as e: rec['error']=str(e)
 with (L/'retrieval.jsonl').open('a') as f:f.write(json.dumps(rec)+'\n')
 print(json.dumps(rec))
if __name__=='__main__':fetch(*sys.argv[1:])
