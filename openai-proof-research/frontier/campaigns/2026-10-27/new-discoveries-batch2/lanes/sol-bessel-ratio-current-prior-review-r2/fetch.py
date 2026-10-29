from pathlib import Path
import urllib.request,urllib.error,datetime,hashlib,json,subprocess
out=Path(__file__).parent; (out/'public').mkdir(exist_ok=True)
urls={
'kvz-final.pdf':'https://link.springer.com/content/pdf/10.1007/s00025-025-02431-4.pdf',
'relosc.pdf':'https://www.mat.univie.ac.at/~gerald/ftp/articles/RelOsc2.pdf',
'order-moment.pdf':'https://arxiv.org/pdf/2606.31647v1',
'derbazi.pdf':'https://arxiv.org/pdf/2502.13136v1',
'qi.pdf':'https://arxiv.org/pdf/1302.6731v1',
'kvz-history.html':'https://arxiv.org/abs/2408.01755',
'karp-publications.html':'https://dmkrp.wordpress.com/publications/'}
with (out/'http.jsonl').open('a') as log:
 for name,url in urls.items():
  rec={'utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'url':url,'file':'public/'+name}
  try:
   with urllib.request.urlopen(urllib.request.Request(url,headers={'User-Agent':'Research review (public read only)'}),timeout=25) as r:
    data=r.read(12000000); rec.update(status=r.status,headers=dict(r.headers),final_url=r.url,bytes=len(data),sha256=hashlib.sha256(data).hexdigest());(out/'public'/name).write_bytes(data)
   if name.endswith('.pdf') and data.startswith(b'%PDF'):subprocess.run(['pdftotext','-layout',str(out/'public'/name),str(out/'public'/name.replace('.pdf','.txt'))],check=True,timeout=20)
  except Exception as e:rec['error']=str(e)
  log.write(json.dumps(rec)+'\n');log.flush();print(name,rec.get('status',rec.get('error')))
