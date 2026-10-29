from pathlib import Path
import urllib.request,subprocess,json
P=Path(__file__).parent;url='https://ghomi.math.gatech.edu/Papers/minkowski.pdf'
try:
 with urllib.request.urlopen(url,timeout=35) as r:b=r.read(8000000)
 (P/'sources/ghomi-spruck.pdf').write_bytes(b);subprocess.run(['pdftotext','-layout',str(P/'sources/ghomi-spruck.pdf'),str(P/'sources/ghomi-spruck.pdf.txt')],check=True)
 out={'url':url,'bytes':len(b),'status':200}
except Exception as e:out={'url':url,'error':str(e)}
(P/'classical-log.json').write_text(json.dumps(out,indent=2)); print(out)
