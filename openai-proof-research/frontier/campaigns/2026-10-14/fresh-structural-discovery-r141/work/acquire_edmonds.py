from research import *
import subprocess
url='https://nvlpubs.nist.gov/nistpubs/jres/69B/jresv69Bn3p147_A1b.pdf';b=urllib.request.urlopen(url,timeout=45).read();assert b.startswith(b'%PDF')
p=PRIVATE/'primary/edmonds-fulkerson-1965.pdf';p.write_bytes(b)
subprocess.run(['pdftotext','-layout',str(p),str(p.with_suffix('.txt'))],check=True)
save('edmonds-acquisition.json',dict(url=url,acquired_utc=now(),size=len(b),sha256=sha(b),text_sha256=sha(p.with_suffix('.txt').read_bytes())))
print('acquired Edmonds-Fulkerson primary')
