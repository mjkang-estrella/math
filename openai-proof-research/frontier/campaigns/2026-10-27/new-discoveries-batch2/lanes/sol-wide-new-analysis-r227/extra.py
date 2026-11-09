from retrieve import *
fetch('https://arxiv.org/pdf/2012.02524v1','gasull.pdf')
p=L/'primary/gasull.txt';h=hashlib.sha256(p.read_bytes()).hexdigest();(L/'gasull-freeze.json').write_text(json.dumps({'path':str(p),'sha256':h}))
s=p.read_text();import re
print(s[:1200])
for m in list(re.finditer(r'Problem \d+\.',s))[:10]:print(s[max(0,m.start()-150):m.start()+1700])
assert hashlib.sha256(p.read_bytes()).hexdigest()==h
