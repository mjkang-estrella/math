import pathlib,json,hashlib,urllib.request,datetime,subprocess
P=pathlib.Path(__file__).resolve().parent;out=json.loads((P/'source-provenance.json').read_text())
for name,url in [('sivaraman-2012','https://etd.ohiolink.edu/acprod/odb_etd/ws/send_file/send?accession=osu1354645035&disposition=inline'),('math-0511635-latest','https://arxiv.org/pdf/math/0511635')]:
 e={'url':url,'utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'version':'2012 thesis' if name.startswith('sivaraman') else 'unversioned latest endpoint; version not yet established'};out.append(e)
 try:
  with urllib.request.urlopen(urllib.request.Request(url,headers={'User-Agent':'Python-urllib/3'}),timeout=35) as f:b=f.read();e['response_url']=f.url
  assert b.startswith(b'%PDF');p=P/(name+'.pdf');p.write_bytes(b);e.update(pdf_path=p.name,pdf_size=len(b),pdf_sha256=hashlib.sha256(b).hexdigest());(P/'source-provenance.json').write_text(json.dumps(out,indent=2)+'\n')
  subprocess.run(['pdftotext','-layout',str(p),str(P/(name+'.txt'))],check=True);b=(P/(name+'.txt')).read_bytes();e.update(text_path=name+'.txt',text_size=len(b),text_sha256=hashlib.sha256(b).hexdigest())
 except Exception as ex:e['failure']=str(ex)
 (P/'source-provenance.json').write_text(json.dumps(out,indent=2)+'\n');print(e)
