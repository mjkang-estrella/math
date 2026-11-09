from pathlib import Path
import json,re,urllib.request,subprocess
R=Path(__file__).resolve().parent;rows=[]
urls=[]
for p in sorted((R/'primary').glob('*.html')):
 m=re.search(r'name="citation_pdf_url" content="([^"]+)"',p.read_text());assert m;urls.append((p.stem,m[1]))
urls.extend([('mss','https://annals.math.princeton.edu/wp-content/uploads/annals-v182-n1-p08-p.pdf'),('moebius','https://arxiv.org/pdf/2308.12641')])
for key,url in urls:
 try:
  with urllib.request.urlopen(url,timeout=25) as f:data=f.read();status=f.status
  assert data.startswith(b'%PDF'),data[:20]
  p=R/'primary'/(key+'.pdf');p.write_bytes(data)
  subprocess.run(['pdftotext','-layout',str(p),str(p.with_suffix('.txt'))],check=True)
  rows.append({'url':url,'file':'primary/'+key+'.pdf','status':status,'extraction':'pdftotext -layout'})
 except Exception as e: rows.append({'url':url,'error':str(e)})
(R/'body-downloads.json').write_text(json.dumps(rows,indent=2)+'\n');print(json.dumps(rows,indent=2))
