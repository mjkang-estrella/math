from pathlib import Path
import urllib.request,urllib.error,datetime,json,hashlib,re,sys
R=Path(__file__).resolve().parents[1];(R/'sources').mkdir(exist_ok=True)
items=[('vpn-successor','https://ir.cwi.nl/pub/26959/a17-goyal.pdf'),('conforti-proof','https://eulersolve.org/papers/owr-2489-009/paper.pdf?v=8f2c5fd65e65'),('bandwidth','https://arxiv.org/pdf/0709.0398')]
log=json.loads((R/'source-provenance.json').read_text())
for name,url in items:
 e={'name':name,'url':url,'requested_utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'version':'live public response'}
 try:
  with urllib.request.urlopen(urllib.request.Request(url,headers={'User-Agent':'Research source verification'}),timeout=25) as r:b=r.read(12000000);e.update(status=r.status,final_url=r.url)
 except urllib.error.HTTPError as x:b=x.read();e.update(status=x.code,error=str(x))
 except Exception as x:b=b'';e.update(error=repr(x))
 e.update(size=len(b),sha256=hashlib.sha256(b).hexdigest(),received_utc=datetime.datetime.now(datetime.timezone.utc).isoformat())
 e['challenge']=bool(re.search(rb'proof.of.work|verify you are human|checking your browser|cf-chl-|captcha|anubis',b[:200000],re.I));e['usable']=e.get('status')==200 and not e['challenge']
 f='sources/'+name+('.pdf' if b.startswith(b'%PDF') else '.html');(R/f).write_bytes(b);e['path']=f;log.append(e)
 (R/'source-provenance.json').write_text(json.dumps(log,indent=2)+'\n')
 print(name,e.get('status'),e['challenge'],e['sha256'],e['size'])
 if e['usable'] and not b.startswith(b'%PDF'):
  print(re.findall(r'href="([^"]+(?:pdf|serial-article-files)[^"]*)"',b.decode(errors='replace')))
