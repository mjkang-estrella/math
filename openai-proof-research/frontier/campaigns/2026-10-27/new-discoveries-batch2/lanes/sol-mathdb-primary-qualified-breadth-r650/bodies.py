import pathlib,json,hashlib,re,urllib.request,datetime,subprocess
D=pathlib.Path(__file__).resolve().parent;out=json.loads((D/'source-provenance.json').read_text());src=[]
for name in ['ems4086','ems3473','ems4135']:
 b=(D/(name+'.html')).read_text();url=re.search(r'name="citation_pdf_url" content="([^"]+)',b).group(1);src.append((name,url))
src += [('acc','https://arxiv.org/pdf/1208.4150v1'),('dvir','https://arxiv.org/pdf/0803.2336v3')]
for name,url in src:
 r={'name':name+'-pdf','url':url,'utc':datetime.datetime.now(datetime.timezone.utc).isoformat()}
 try:
  with urllib.request.urlopen(urllib.request.Request(url,headers={'User-Agent':'Python-urllib/3'}),timeout=25) as f:b=f.read();r['final_url']=f.url
  assert b.startswith(b'%PDF');p=D/(name+'.pdf');p.write_bytes(b);r.update(path=str(p),sha256=hashlib.sha256(b).hexdigest(),size=len(b),status='bound_before_extraction')
  out.append(r);(D/'source-provenance.json').write_text(json.dumps(out,indent=2)+'\n')
  t=D/(name+'.txt');subprocess.run(['pdftotext','-layout',str(p),str(t)],check=True);c=t.read_bytes();out.append({'name':name+'-text','path':str(t),'sha256':hashlib.sha256(c).hexdigest(),'size':len(c),'derived_from':r['sha256'],'status':'bound_before_read'})
 except Exception as e:r.update(status='STOP',error=str(e));out.append(r)
 (D/'source-provenance.json').write_text(json.dumps(out,indent=2)+'\n')
print(json.dumps(out[-10:],indent=2))
