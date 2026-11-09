import pathlib,json,urllib.request,datetime,hashlib,re,subprocess
P=pathlib.Path(__file__).resolve().parent
log=json.loads((P/'fetch-provenance.json').read_text());bindings=json.loads((P/'download-bindings.json').read_text())
def bind(p):
 b=p.read_bytes();bindings.append({'path':str(p.resolve()),'size':len(b),'sha256':hashlib.sha256(b).hexdigest()});(P/'download-bindings.json').write_text(json.dumps(bindings,indent=2)+'\n')
urls=[]
for n in ['1190','1274','1386','1452','1453','1394']:
 s=(P/('ems'+n+'.html')).read_text();url=re.search(r'name="citation_pdf_url" content="([^"]+)"',s)[1];urls.append((url,'ems'+n))
urls += [('https://arxiv.org/pdf/math/0602258v1','hille-perling-v1'),('https://arxiv.org/pdf/0909.4639v1','powers-v1'),('https://myweb.uoi.gr/abeligia/vGorenstein_final.pdf','gorenstein-author')]
for url,name in urls:
 e={'url':url,'utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'file':name+'.pdf'}
 try:
  with urllib.request.urlopen(urllib.request.Request(url,headers={'User-Agent':'ResearchReader/1.0','Accept':'application/pdf'}),timeout=20) as r:b=r.read(10000000);e.update(status=r.status,final_url=r.url)
  p=P/e['file'];p.write_bytes(b);bind(p);e.update(size=len(b),sha256=hashlib.sha256(b).hexdigest())
  subprocess.run(['pdftotext','-layout',str(p),str(P/(name+'.txt'))],check=True);bind(P/(name+'.txt'));print(name,'OK')
 except Exception as ex:e['error']=str(ex);print(name,e['error'])
 log.append(e);(P/'fetch-provenance.json').write_text(json.dumps(log,indent=2)+'\n')
