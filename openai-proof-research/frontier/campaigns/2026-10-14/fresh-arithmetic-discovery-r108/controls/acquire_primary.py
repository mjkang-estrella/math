from pathlib import Path
import urllib.request,hashlib,json,subprocess,concurrent.futures
ROOT=Path(__file__).resolve().parents[1]
urls={
'erdos1958':'https://www.cambridge.org/core/services/aop-cambridge-core/content/view/AE51B28BC5E3C79E58C6C3ED7122395C/S0008439500050104a.pdf/on_an_elementary_problem_in_number_theory.pdf',
'chalk-erdos1959':'https://www.renyi.hu/~p_erdos/1959-14.pdf',
'hidden-forests2018v2':'https://arxiv.org/pdf/1805.03186v2',
}
def get(kv):
 name,url=kv;out=ROOT/'private/primary'/(name+'.pdf');rec={'name':name,'url':url}
 try:
  with urllib.request.urlopen(url,timeout=40) as r:b=r.read();rec['final_url']=r.url
  assert b.startswith(b'%PDF')
  out.write_bytes(b);rec.update(bytes=len(b),sha256=hashlib.sha256(b).hexdigest(),status='acquired')
  subprocess.run(['pdftotext','-layout',str(out),str(out.with_suffix('.txt'))],check=True,timeout=25)
  rec['text_sha256']=hashlib.sha256(out.with_suffix('.txt').read_bytes()).hexdigest()
 except Exception as e:rec.update(status='failed',error=repr(e))
 return rec
with concurrent.futures.ThreadPoolExecutor(max_workers=3) as ex:rec=list(ex.map(get,urls.items()))
(ROOT/'private/primary-metadata.json').write_text(json.dumps(rec,indent=2));print(json.dumps(rec,indent=2))
