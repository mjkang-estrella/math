from retrieve import get,L,P
import subprocess,hashlib,json,urllib.parse,xml.etree.ElementTree as E
get('https://pages.uoregon.edu/mbownik/papers/16.pdf','bownik-weber-2003.pdf')
get('https://arxiv.org/pdf/2507.09818v2','bownik-2025.pdf')
get('https://export.arxiv.org/api/query?search_query='+urllib.parse.quote('ti:"open problems" AND (cat:math.MG OR cat:math.CA)')+'&max_results=25&sortBy=submittedDate&sortOrder=descending','breadth.xml')
rows=[]
for p in P.glob('*.pdf'):
 before=hashlib.sha256(p.read_bytes()).hexdigest();q=p.with_suffix('.txt')
 subprocess.run(['pdftotext','-layout',str(p),str(q)],check=True)
 assert before==hashlib.sha256(p.read_bytes()).hexdigest()
 rows.append(dict(pdf=str(p),sha256=before,text=str(q),text_sha256=hashlib.sha256(q.read_bytes()).hexdigest()))
(L/'text-bindings.json').write_text(json.dumps(rows,indent=2))
for p in P.glob('*.txt'):
 s=p.read_text();print(p.name)
 lines=s.splitlines()
 for i,line in enumerate(lines):
  if any(t in line.lower() for t in ['1/6','1/8','1/4','problem','question','conjecture','characteristic function']):print(i,'\n'.join(lines[max(0,i-2):i+7]))
