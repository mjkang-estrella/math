from retrieve import get,L,P
import urllib.parse,subprocess,hashlib,json,xml.etree.ElementTree as E
for name,q in [('scout-current','(au:Grabner AND all:singular) OR (au:Bilyk AND all:torus) OR (au:Steinerberger AND all:Hadamard) OR (au:Marzo AND all:weights)'),('annulus-current','(all:wavelet AND (all:annular OR all:annulus)) OR (au:Weber AND au:Bownik)')]:
 get('https://export.arxiv.org/api/query?search_query='+urllib.parse.quote(q)+'&max_results=20&sortBy=submittedDate&sortOrder=descending',name+'.xml')
get('https://arxiv.org/pdf/2410.22104v1','grabner.pdf')
p=P/'grabner.pdf'
if p.exists():
 q=p.with_suffix('.txt');h=hashlib.sha256(p.read_bytes()).hexdigest();subprocess.run(['pdftotext','-layout',str(p),str(q)],check=True)
 assert h==hashlib.sha256(p.read_bytes()).hexdigest()
 (L/'grabner-binding.json').write_text(json.dumps({'pdf_sha256':h,'text_sha256':hashlib.sha256(q.read_bytes()).hexdigest()}))
 lines=q.read_text().splitlines()
 for i,s in enumerate(lines):
  if any(t in s for t in ['Theorem','Corollary','positive s','s > 0','s∗','s*','conjecture']):print(i,'\n'.join(lines[max(0,i-2):i+12]))
