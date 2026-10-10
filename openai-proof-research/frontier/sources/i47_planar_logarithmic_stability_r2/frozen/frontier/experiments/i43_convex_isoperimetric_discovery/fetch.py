from pathlib import Path
import requests,json,hashlib,concurrent.futures,subprocess,datetime
S=Path(__file__).resolve().parents[2]/'sources/i43_convex_isoperimetric_discovery'
D=S/'literature';D.mkdir(exist_ok=True)
items=[('blyz2012','https://math.nyu.edu/~yangd/papers/LBMI.pdf'),('bk2022','https://arxiv.org/pdf/2002.12239v2'),('bd2025','https://arxiv.org/pdf/2101.02549v6'),('lu2026','https://arxiv.org/pdf/2608.20730v3'),('putterman','https://arxiv.org/pdf/1909.03729'),('km','https://arxiv.org/pdf/1711.01089'),('vanhandel','https://web.math.princeton.edu/~rvan/logzon221121.pdf'),('milman','https://arxiv.org/pdf/2403.06602v3'),('afm','https://cvgmt.sns.it/media/doc/paper/540/Acerbi-Fusco-Morini.FINAL.pdf'),('reverseprojection','https://archive.ymsc.tsinghua.edu.cn/pacm_download/743/12781--2026.8.26.pdf'),('saroglou','https://arxiv.org/pdf/1409.4346')]
def get(item):
 name,url=item; rec={'name':name,'url':url,'retrieved_utc':datetime.datetime.now(datetime.timezone.utc).isoformat()}
 try:
  r=requests.get(url,timeout=35);rec.update(status=r.status_code,final_url=r.url,headers=dict(r.headers),sha256=hashlib.sha256(r.content).hexdigest());ext='.pdf' if r.content.startswith(b'%PDF') else '.response';p=D/(name+ext);p.write_bytes(r.content);rec['file']=str(p.relative_to(S));rec['ok']=r.status_code==200 and ext=='.pdf'
  if rec['ok']:subprocess.run(['pdftotext','-layout',str(p),str(D/(name+'.txt'))],check=True)
 except Exception as ex:rec.update(ok=False,error=str(ex))
 return rec
with concurrent.futures.ThreadPoolExecutor(max_workers=6) as ex: rows=list(ex.map(get,items))
(S/'responses.json').write_text(json.dumps(rows,indent=2)+'\n')
for r in rows:print(r['name'],r['ok'],r.get('status'),r.get('error',''))
