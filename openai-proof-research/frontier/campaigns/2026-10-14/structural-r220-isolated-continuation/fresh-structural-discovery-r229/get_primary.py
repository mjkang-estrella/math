from pathlib import Path
import urllib.request,subprocess,json,hashlib,concurrent.futures,re
R=Path(__file__).resolve().parent;D=R/'private/primary';D.mkdir(exist_ok=True)
items=[('TW2000','https://maths-people.anu.edu.au/~wang/publications/1-Invent00.pdf'),('TW2002','https://maths-people.anu.edu.au/~wang/publications/2-Invent02.pdf'),('TW2005','https://arxiv.org/pdf/math/0405541v1'),('Du2024','https://arxiv.org/pdf/2210.09127v2'),('Sun2026','https://arxiv.org/pdf/2608.25330v1'),('TW2026','https://arxiv.org/pdf/2610.09385v1'),('Calabi1982','https://www.jstor.org/stable/pdf/2374069.pdf')]
def get(it):
 name,url=it;row={'name':name,'url':url}
 try:
  b=urllib.request.urlopen(url,timeout=35).read();row.update(bytes=len(b),sha256=hashlib.sha256(b).hexdigest());(D/(name+'.pdf')).write_bytes(b)
  if not b.startswith(b'%PDF'):raise ValueError('Not PDF')
  p=subprocess.run(['pdftotext','-layout',str(D/(name+'.pdf')),str(D/(name+'.txt'))],capture_output=True,timeout=30);row['extraction_code']=p.returncode
  if p.returncode:row['error']=p.stderr.decode()[:200]
  else:
   text=(D/(name+'.txt')).read_bytes();row['text_bytes']=len(text);row['pages']=text.count(b'\f');row['text_sha256']=hashlib.sha256(text).hexdigest()
 except Exception as e:row['error']=str(e)
 return row
with concurrent.futures.ThreadPoolExecutor(max_workers=4) as ex:rows=list(ex.map(get,items))
(R/'primary-access.json').write_text(json.dumps(rows,indent=2)+'\n');print(json.dumps(rows,indent=2))
for row in rows:
 f=D/(row['name']+'.txt')
 if not f.exists():continue
 b=f.read_bytes();print('\nBOUNDARY',row['name']);off=0
 for i,l in enumerate(b.splitlines(keepends=True),1):
  st=l.strip()
  if re.search(rb'acknow|thank|licen[cs]e|copyright|all rights|communicat|supported by|e-mail|email|oblatum|published online|download|publisher',l,re.I):print(i,off,off+len(l),'EDITORIAL-MARKER')
  elif re.match(rb'(?:[1-9][0-9]?\.|[A-Z]\.|\xc2\xa7\s*[1-9])\s+[A-Za-z]',st) or re.match(rb'(?:References|REFERENCE|Appendix|Introduction|Conclusion)',st):print(i,off,off+len(l),st.decode())
  off+=len(l)
