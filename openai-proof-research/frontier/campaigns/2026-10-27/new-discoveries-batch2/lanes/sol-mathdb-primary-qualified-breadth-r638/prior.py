import urllib.request,pathlib,json,hashlib,datetime,subprocess
P=pathlib.Path(__file__).resolve().parent;url='https://arxiv.org/pdf/math/0407108v1';out={ 'url':url,'utc':datetime.datetime.now(datetime.timezone.utc).isoformat()}
try:
 with urllib.request.urlopen(urllib.request.Request(url,headers={'User-Agent':'Mozilla/5.0','Accept':'application/pdf'}),timeout=25) as r:b=r.read();out['final_url']=r.url
 p=P/'0407108v1.pdf';p.write_bytes(b);out.update(path=p.name,size=len(b),sha256=hashlib.sha256(b).hexdigest());(P/'prior-bindings.json').write_text(json.dumps(out,indent=2)+'\n');assert b.startswith(b'%PDF');subprocess.run(['pdftotext','-layout',str(p),str(p.with_suffix('.txt'))],check=True);b=p.with_suffix('.txt').read_bytes();(P/'prior-derivative.json').write_text(json.dumps(dict(path=p.with_suffix('.txt').name,size=len(b),sha256=hashlib.sha256(b).hexdigest()),indent=2)+'\n')
except Exception as e:out['error']=str(e);(P/'prior-bindings.json').write_text(json.dumps(out,indent=2)+'\n')
print(json.dumps(out))
