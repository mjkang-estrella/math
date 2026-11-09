from pathlib import Path
import urllib.request,hashlib,json,datetime,re,subprocess
D=Path(__file__).parent;prov=json.loads((D/'source-provenance.json').read_text());der=[]
for n in ['1452','1111','1464']:
 p=D/('owr'+n+'.html'); old=next(x for x in prov if x['path']==str(p.resolve()));assert hashlib.sha256(p.read_bytes()).hexdigest()==old['sha256']
 u=re.search(r'https://content.ems.press/[^"<>\\ ]+\.pdf',p.read_text()).group();t=datetime.datetime.now(datetime.timezone.utc).isoformat()
 try:
  with urllib.request.urlopen(u,timeout=25) as f:b=f.read();final=f.url
  pdf=D/('owr'+n+'.pdf');pdf.write_bytes(b);prov.append(dict(url=u,final_url=final,utc=t,path=str(pdf.resolve()),size=len(b),sha256=hashlib.sha256(b).hexdigest(),version='published OWR report, exact URL'))
  (D/'source-provenance.json').write_text(json.dumps(prov,indent=2)+'\n')
  assert b.startswith(b'%PDF');txt=D/('owr'+n+'.txt');subprocess.run(['pdftotext','-layout',str(pdf),str(txt)],check=True)
  z=txt.read_bytes();der.append(dict(path=str(txt.resolve()),size=len(z),sha256=hashlib.sha256(z).hexdigest(),derived_from=str(pdf.resolve()),command='pdftotext -layout'))
 except Exception as e:prov.append(dict(url=u,utc=t,failure=str(e)))
(D/'source-provenance.json').write_text(json.dumps(prov,indent=2)+'\n');(D/'derivative-bindings.json').write_text(json.dumps(der,indent=2)+'\n');print('bound derivatives',len(der))
