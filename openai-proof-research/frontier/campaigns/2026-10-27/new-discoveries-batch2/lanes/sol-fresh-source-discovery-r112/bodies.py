from pathlib import Path
import urllib.request,hashlib,json,datetime,subprocess
L=Path(__file__).parent
with (L/'bodies-http.jsonl').open('w') as log:
 for name,url in [('bg2a','https://people.math.binghamton.edu/zaslav/Tpapers/bg2a.jctb1991.pdf'),('bg2b','https://people.math.binghamton.edu/zaslav/Tpapers/bg2b.jctb1991.pdf')]:
  row={'name':name,'url':url,'utc':datetime.datetime.now(datetime.timezone.utc).isoformat()}
  try:
   h=hashlib.sha256();n=0
   with urllib.request.urlopen(url,timeout=25) as r,(L/'inputs'/f'{name}.pdf').open('wb') as out:
    row['status']=r.status
    while b:=r.read(32768):out.write(b);h.update(b);n+=len(b)
   row.update(bytes=n,sha256=h.hexdigest())
   subprocess.run(['pdftotext','-layout',str(L/'inputs'/f'{name}.pdf'),str(L/'inputs'/f'{name}.txt')],check=True)
  except Exception as e:row['error']=str(e)
  log.write(json.dumps(row)+'\n');log.flush()
subprocess.run(['pdftotext','-layout',str(L/'inputs/ahk.pdf'),str(L/'inputs/ahk.txt')],check=True)
