import pathlib,urllib.request,datetime,hashlib,json,resource,os,subprocess
P=pathlib.Path(__file__).resolve().parent
resource.setrlimit(resource.RLIMIT_CPU,(120,120));resource.setrlimit(resource.RLIMIT_AS,(6*1024**3,6*1024**3));os.sched_setaffinity(0,sorted(os.sched_getaffinity(0))[:2])
u='https://zenodo.org/records/23605839/files/Goel_Cranston_Li_Su_Wang_Xu_conjecture_is_true_with_extensions.pdf?download=1'
r={'url':u,'utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'reason':'Standard download link explicitly advertised in successfully fetched record; earlier HTTP 200 PDF is unreadable, not access-denied.'}
try:
 with urllib.request.urlopen(u,timeout=15) as f:b=f.read(10*1024**2);r.update(status=f.status,bytes=len(b),sha256=hashlib.sha256(b).hexdigest(),headers=dict(f.headers));(P/'goel-expanded-download.pdf').write_bytes(b)
 q=subprocess.run(['pdftotext','-layout',str(P/'goel-expanded-download.pdf'),str(P/'goel-expanded-download.txt')],capture_output=True,timeout=20);r.update(text_exit=q.returncode,stderr=q.stderr.decode(errors='replace'))
except Exception as e:r['error']=repr(e)
with (P/'fetch-receipts.jsonl').open('a') as f:f.write(json.dumps(r)+'\n')
print(json.dumps(r))
