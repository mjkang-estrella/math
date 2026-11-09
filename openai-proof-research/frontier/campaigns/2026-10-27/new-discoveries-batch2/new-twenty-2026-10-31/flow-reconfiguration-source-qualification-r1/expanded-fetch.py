import pathlib,urllib.request,datetime,json,hashlib,resource,os,re,subprocess
P=pathlib.Path(__file__).resolve().parent
resource.setrlimit(resource.RLIMIT_CPU,(120,120)); resource.setrlimit(resource.RLIMIT_AS,(6*1024**3,6*1024**3)); os.sched_setaffinity(0,sorted(os.sched_getaffinity(0))[:2])
def get(url,name):
 r={'url':url,'utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'destination':str(P/name)}
 try:
  with urllib.request.urlopen(url,timeout=15) as f:b=f.read(12*1024**2);r.update(status=f.status,final_url=f.url,bytes=len(b),sha256=hashlib.sha256(b).hexdigest());(P/name).write_bytes(b)
 except Exception as e:r['error']=repr(e);b=b''
 with (P/'fetch-receipts.jsonl').open('a') as f:f.write(json.dumps(r)+'\n')
 print(name,r.get('status',r.get('error')),flush=True);return b
b=get('https://zenodo.org/records/23605839','goel-expanded-record.html')
urls=re.findall(rb'https://zenodo.org/records/23605839/files/[^"<> ]+\.pdf',b)
if urls:
 u=urls[0].decode().replace('&amp;','&'); b=get(u,'goel-expanded.pdf')
 if b:subprocess.run(['pdftotext','-layout',str(P/'goel-expanded.pdf'),str(P/'goel-expanded.txt')],timeout=20,check=True)
