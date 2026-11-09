import pathlib,urllib.request,hashlib,subprocess,json
O=pathlib.Path('frontier/campaigns/2026-10-14/fresh-structural-discovery-r125');P=O/'packet/private/primary';rec=[]
for name,url in [('jiang','https://arxiv.org/pdf/2610.18884v1'),('gaitonde-mossel','https://arxiv.org/pdf/2410.11136v2'),('jonasson','https://arxiv.org/pdf/1210.6916v2'),('bowler-geschke','https://www.math.uni-hamburg.de/home/geschke/papers/UniformMatroid7.pdf')]:
 try:
  b=urllib.request.urlopen(url,timeout=30).read();assert b.startswith(b'%PDF');p=P/(name+'.pdf');p.write_bytes(b);r=subprocess.run(['pdftotext','-layout',str(p),str(p.with_suffix('.txt'))],capture_output=True);rec.append(dict(name=name,url=url,bytes=len(b),sha256=hashlib.sha256(b).hexdigest(),text_sha256=hashlib.sha256(p.with_suffix('.txt').read_bytes()).hexdigest(),extraction_returncode=r.returncode))
 except Exception as e: rec.append(dict(name=name,url=url,error=str(e)))
(P/'register.json').write_text(json.dumps(rec,indent=2)+'\n');print(rec)
