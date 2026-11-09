from pathlib import Path
import urllib.request,json,subprocess,datetime
R=Path(__file__).resolve().parent
urls={'foliations':'https://arxiv.org/pdf/1305.1287','ellipsoids':'https://arxiv.org/pdf/0912.0532','integer-homology':'https://arxiv.org/pdf/1808.10647'}
out=[]
for n,u in urls.items():
 d={'name':n,'url':u,'date':datetime.datetime.now(datetime.timezone.utc).isoformat()}
 try:
  with urllib.request.urlopen(u,timeout=25) as f:b=f.read()
  assert b.startswith(b'%PDF');(R/f'sources/{n}.pdf').write_bytes(b)
  c=subprocess.run(['pdftotext','-layout',str(R/f'sources/{n}.pdf'),str(R/f'sources/{n}.txt')],capture_output=True);d.update(status='downloaded',extract_returncode=c.returncode)
 except Exception as e:d.update(status='HOLD',error=str(e))
 out.append(d)
(R/'successor2-provenance.json').write_text(json.dumps(out,indent=2)+'\n');print(out)
