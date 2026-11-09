import pathlib,urllib.request,subprocess,json,hashlib
O=pathlib.Path(__file__).parent;url='https://web.math.princeton.edu/~mchudnov/containers.pdf'
try:
 with urllib.request.urlopen(url,timeout=25) as f:d=f.read(12000000)
 assert d.startswith(b'%PDF');p=O/'sources/containers.pdf';p.write_bytes(d);subprocess.run(['pdftotext','-layout',str(p),str(p.with_suffix('.txt'))],check=True)
 j=dict(url=url,size=len(d),sha256=hashlib.sha256(d).hexdigest(),status=200,path='sources/containers.pdf')
except Exception as e:j=dict(url=url,error=str(e))
(O/'container-provenance.json').write_text(json.dumps(j,indent=2)+'\n');print(j)
