from pathlib import Path
import sys,json,hashlib,urllib.request,datetime,subprocess
L=Path(__file__).resolve().parent
def sha(p): return hashlib.sha256(p.read_bytes()).hexdigest()
def fetch(ids):
 for ident in ids:
  u='https://arxiv.org/pdf/'+ident;p=L/'retrieved'/f'{ident}.pdf';q=L/'source'/p.name
  rec={'url':u,'time':datetime.datetime.now(datetime.timezone.utc).isoformat()}
  try:
   with urllib.request.urlopen(u,timeout=18) as r:
    rec['status']=r.status;d=r.read(9000000)
   if not d.startswith(b'%PDF'): raise ValueError('non-PDF; stop this route')
   p.write_bytes(d);q.write_bytes(d);rec.update(original=str(p),copy=str(q),sha256=sha(p));assert sha(q)==sha(p)
   with (L/'provenance.jsonl').open('a') as f:f.write(json.dumps(rec)+'\n')
   out=L/'source'/f'{ident}.txt';subprocess.run(['pdftotext','-layout',str(q),str(out)],check=True,timeout=15)
   assert sha(p)==sha(q)==rec['sha256'];print(ident,'OK',flush=True)
  except Exception as e:
   rec['error']=str(e)
   with (L/'failures.jsonl').open('a') as f:f.write(json.dumps(rec)+'\n')
   print(ident,'FAIL',str(e),flush=True)
if __name__=='__main__':fetch(sys.argv[1:])
