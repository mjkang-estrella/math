from pathlib import Path
import urllib.request,hashlib,json,datetime,subprocess,concurrent.futures
root=Path(__file__).resolve().parents[3];out=root/'frontier/sources/i07_structures/literature';out.mkdir(exist_ok=True)
sources=[('block-weinberger','https://math.uchicago.edu/~shmuel/Nielsen.pdf','pdf'),('kaniewski-lee-dewolf','https://homepages.cwi.nl/~rdewolf/publ/qc/query_expectation-arxiv.pdf','pdf'),('leary-almost-fp','https://d-nb.info/1162825146/34','pdf'),('davis-hayden-huang-ruberman-sunukjian','https://people.math.osu.edu/davis.12/papers/dhhrs.pdf','pdf'),('daura-serrano','https://arxiv.org/pdf/2407.13602','pdf'),('bartels-lueck','https://arxiv.org/pdf/0901.0442','pdf')]
def get(s):
 name,url,ext=s;rec=dict(name=name,url=url,retrieved_utc=datetime.datetime.now(datetime.timezone.utc).isoformat())
 try:
  data=urllib.request.urlopen(url,timeout=60).read();dest=out/(name+'.'+ext);dest.write_bytes(data);rec.update(file=str(dest.relative_to(root)),sha256=hashlib.sha256(data).hexdigest(),bytes=len(data))
  if data.startswith(b'%PDF'):
   txt=dest.with_suffix('.txt');subprocess.run(['pdftotext','-layout',str(dest),str(txt)],check=True);rec['text_sha256']=hashlib.sha256(txt.read_bytes()).hexdigest()
  else:rec['warning']='Not a PDF'
 except Exception as e:rec['error']=str(e)
 return rec
with concurrent.futures.ThreadPoolExecutor(max_workers=6) as pool:records=list(pool.map(get,sources))
(out/'manifest.json').write_text(json.dumps(records,indent=2)+'\n');print(json.dumps(records,indent=2))
