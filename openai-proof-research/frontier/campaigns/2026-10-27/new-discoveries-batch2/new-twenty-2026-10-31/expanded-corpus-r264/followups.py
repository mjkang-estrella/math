from pathlib import Path
import json,hashlib,datetime,urllib.request,concurrent.futures,resource,subprocess,re,time
resource.setrlimit(resource.RLIMIT_CPU,(120,120));resource.setrlimit(resource.RLIMIT_AS,(6*1024**3,6*1024**3))
p=Path(__file__).resolve().parent; data=json.loads((p/'literal-provenance.json').read_text()); (p/'sources').mkdir(exist_ok=True)
def run(pair):
 name,url=pair;rec={'label':name,'url':url,'utc':datetime.datetime.now(datetime.timezone.utc).isoformat()}
 try:
  with urllib.request.urlopen(url,timeout=20) as r:b=r.read(15000000);rec.update(status=r.status,final_url=r.url,sha256=hashlib.sha256(b).hexdigest(),bytes=len(b));f=p/'sources'/name;f.write_bytes(b)
  if b.startswith(b'%PDF'):subprocess.run(['pdftotext','-layout',str(f),str(f)+'.txt'],timeout=20,check=True)
 except Exception as e:rec['error']=str(e)
 return rec
u={'ems-report':'https://ems.press/content/serial-article-files/46314?nt=1','pool-current-projects':'https://raw.githubusercontent.com/Vilin97/lean-pool/main/LeanPool/projects.yml','tree-claim':'https://arxiv.org/pdf/2610.02271','tree-claim-abs':'https://arxiv.org/abs/2610.02271','radical-proof':'https://cmup.fc.up.pt/cmup/jalmeida/preprints/Fitting.pdf','genus-journal':'https://people.smp.uq.edu.au/OleWarnaar/pubs/HRV.pdf','gilbey-journal':'https://www.kurims.kyoto-u.ac.jp/EMIS/journals/JACO/Volume19_1/wr68l4x68836477w.fulltext.pdf'}
with concurrent.futures.ThreadPoolExecutor(max_workers=2) as ex:rows=list(ex.map(run,u.items()))
(p/'followup-receipts.json').write_text(json.dumps(rows,indent=2));print(json.dumps(rows,indent=2))
