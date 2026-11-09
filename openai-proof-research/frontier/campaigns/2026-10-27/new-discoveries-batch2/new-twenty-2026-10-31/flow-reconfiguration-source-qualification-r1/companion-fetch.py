import pathlib,urllib.request,datetime,hashlib,json,resource,os,re,subprocess
P=pathlib.Path(__file__).resolve().parent
resource.setrlimit(resource.RLIMIT_CPU,(120,120));resource.setrlimit(resource.RLIMIT_AS,(6*1024**3,6*1024**3));os.sched_setaffinity(0,sorted(os.sched_getaffinity(0))[:2])
def get(u,n):
 r={'url':u,'utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'destination':str(P/n)}
 try:
  with urllib.request.urlopen(u,timeout=18) as f:b=f.read(10*1024**2);r.update(status=f.status,bytes=len(b),sha256=hashlib.sha256(b).hexdigest());(P/n).write_bytes(b)
 except Exception as e:r['error']=repr(e);b=b''
 with (P/'fetch-receipts.jsonl').open('a') as f:f.write(json.dumps(r)+'\n')
 print(n,r.get('status',r.get('error')),flush=True);return b
b=get('https://zenodo.org/records/23605809','companion-record.html')
m=re.search(rb'name="citation_pdf_url" content="([^"]+)"',b)
if m:
 b=get(m[1].decode()+'?download=1','companion.pdf')
 if b:
  r=subprocess.run(['pdftotext','-layout',str(P/'companion.pdf'),str(P/'companion.txt')],capture_output=True,timeout=25);(P/'companion-text-status.json').write_text(json.dumps({'exit':r.returncode,'stderr':r.stderr.decode(errors='replace')}));print('text exit',r.returncode)
