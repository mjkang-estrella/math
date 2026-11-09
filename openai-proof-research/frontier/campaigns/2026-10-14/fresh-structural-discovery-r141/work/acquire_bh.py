from research import *
import subprocess
url='https://web.math.princeton.edu/~huh/Lorentzian.pdf'
b=urllib.request.urlopen(url,timeout=50).read();assert b.startswith(b'%PDF')
p=PRIVATE/'primary/branden-huh.pdf';p.write_bytes(b)
subprocess.run(['pdftotext','-layout',str(p),str(p.with_suffix('.txt'))],check=True)
save('bh-acquisition.json',dict(url=url,acquired_utc=now(),size=len(b),sha256=sha(b),text_sha256=sha(p.with_suffix('.txt').read_bytes())))
print('acquired BH primary')
