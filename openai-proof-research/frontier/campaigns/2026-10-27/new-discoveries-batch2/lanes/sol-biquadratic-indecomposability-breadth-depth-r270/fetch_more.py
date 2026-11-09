from pathlib import Path
import urllib.request,json,hashlib,subprocess
L=Path(__file__).resolve().parent
urls=[('man-query','https://export.arxiv.org/api/query?search_query=all:%22Minimal%20rank%22%20AND%20all:multiquadratic&max_results=5'),('man-author','https://export.arxiv.org/api/query?search_query=au:Man%20AND%20all:indecomposable&max_results=10')]
if __name__=='__main__':
 import sys
 if len(sys.argv)>1:urls=[(sys.argv[1],sys.argv[2])]
 logs=[]
 for name,url in urls:
  try:
   with urllib.request.urlopen(url,timeout=25) as r:data=r.read(10000000);status=r.status
   p=L/'sources'/(name+('.pdf' if data.startswith(b'%PDF') else '.html'));p.write_bytes(data)
   logs.append(dict(url=url,status=status,path=str(p.relative_to(L)),sha256=hashlib.sha256(data).hexdigest()))
   if data.startswith(b'%PDF'):subprocess.run(['pdftotext','-layout',str(p),str(p.with_suffix('.txt'))],check=True,timeout=25)
  except Exception as e:logs.append(dict(url=url,error=repr(e)))
 with (L/'more-access.jsonl').open('a') as f:
  for row in logs:f.write(json.dumps(row)+'\n')
 print(json.dumps(logs))
