import urllib.request,hashlib,json,datetime,subprocess
from pathlib import Path
O=Path(__file__).resolve().parent
sources={
'pinelis':'https://pages.mtu.edu/~ipinelis/lhosp/monthly.pdf',
'hirschman':'https://www.cambridge.org/core/services/aop-cambridge-core/content/view/01E4F067C2CE787EFB8FD834F214512F/S0008414X00035197a.pdf/variation-diminishing-transformations-and-general-orthogonal-polynomials.pdf',
'lusztig':'https://arxiv.org/pdf/0705.3842v1',
'author-source':'https://www.dmg.tuwien.ac.at/drmota/CDG241.pdf',
'publisher':'https://www.cambridge.org/core/journals/european-journal-of-applied-mathematics/article/modelling-silicosis-the-structure-of-equilibria/AC58FD8015664FDC506CB871E3C8F754',
}
records=[]
for name,url in sources.items():
 r={'url':url,'utc':datetime.datetime.now(datetime.timezone.utc).isoformat()}
 try:
  with urllib.request.urlopen(url,timeout=25) as f:
   r.update(status=f.status,final_url=f.url,headers=dict(f.headers)); h=hashlib.sha256();total=0
   path=O/(name+('.pdf' if name!='publisher' else '.html'))
   with path.open('wb') as out:
    while b:=f.read(65536):
     total+=len(b);assert total<20000000;out.write(b);h.update(b)
   r.update(bytes=total,sha256=h.hexdigest(),file=path.name)
   if name!='publisher':subprocess.run(['pdftotext','-layout',str(path),str(O/(name+'.txt'))],check=True)
 except Exception as e:r['failure']=repr(e)
 records.append(r)
(O/'fetch-records.json').write_text(json.dumps(records,indent=2))
print(json.dumps([{k:v for k,v in r.items() if k!='headers'} for r in records],indent=2))
