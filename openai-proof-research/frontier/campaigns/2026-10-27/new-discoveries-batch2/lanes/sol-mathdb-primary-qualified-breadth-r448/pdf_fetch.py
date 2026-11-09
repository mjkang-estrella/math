import pathlib,json,urllib.request,re,hashlib,subprocess
O=pathlib.Path(__file__).parent;routes=[]
for p in sorted((O/'sources').glob('*.html')):
 url=re.search(r'https[^"<>\s]+\.pdf',p.read_text()).group().replace('\\','');routes.append((p.stem,url))
routes += [('MM-successor','https://ivv5hpp.uni-muenster.de/u/rds/MM_implies_star_final_version_March_18_2021.pdf'),('MWIS-successor','https://web.math.princeton.edu/~mchudnov/holePMC.pdf')]
out=[]
for n,url in routes:
 try:
  with urllib.request.urlopen(url,timeout=25) as f:data=f.read(12000000);status=f.status
  assert data.startswith(b'%PDF')
  p=O/'sources'/(n+'.pdf');p.write_bytes(data)
  c=subprocess.run(['pdftotext','-layout',str(p),str(p.with_suffix('.txt'))],capture_output=True,text=True)
  out.append(dict(url=url,status=status,path=str(p.relative_to(O)),sha256=hashlib.sha256(data).hexdigest(),size=len(data),extraction_returncode=c.returncode,extraction_stderr=c.stderr))
 except Exception as e:out.append(dict(url=url,error=str(e)))
(O/'pdf-provenance.json').write_text(json.dumps(out,indent=2)+'\n');print(json.dumps(out,indent=2))
