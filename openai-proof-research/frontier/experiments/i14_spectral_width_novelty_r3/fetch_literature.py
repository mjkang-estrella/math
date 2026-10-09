import pathlib,json,hashlib,urllib.request,concurrent.futures,subprocess,datetime
out=pathlib.Path('frontier/sources/i14_spectral_width_novelty_r3/literature');out.mkdir(parents=True,exist_ok=True)
items=[('chai-sun-band-v2','https://arxiv.org/pdf/2504.10142v2'),('gromov-four-v6','https://arxiv.org/pdf/1908.10612v6'),('gromov-stabilized','https://www.emis.de/journals/SIGMA/2024/038/sigma24-038.pdf'),('liokumovich-wang-v1','https://arxiv.org/pdf/2308.04044v1'),('chai-chen-pyo-v1','https://arxiv.org/pdf/2606.19858v1'),('chodosh-li','https://arxiv.org/pdf/2008.11888'),('chai-sun-rigidity-v1','https://arxiv.org/pdf/2604.04052v1')]
def get(item):
 name,url=item
 try:
  b=urllib.request.urlopen(url,timeout=50).read();p=out/(name+'.pdf');p.write_bytes(b);subprocess.run(['pdftotext','-layout',str(p),str(out/(name+'.txt'))],check=True);return {'name':name,'url':url,'sha256':hashlib.sha256(b).hexdigest(),'bytes':len(b),'retrieved_utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'status':'downloaded'}
 except Exception as e:return {'name':name,'url':url,'error':str(e)}
with concurrent.futures.ThreadPoolExecutor(max_workers=7) as pool: rows=list(pool.map(get,items))
(out/'manifest.json').write_text(json.dumps(rows,indent=2)+'\n');print(json.dumps(rows,indent=2))
