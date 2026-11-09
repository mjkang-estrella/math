from pathlib import Path
import hashlib,json,subprocess,datetime,urllib.request,urllib.error
O=Path(__file__).parent; B=O.parent
def sha(p): return hashlib.sha256(p.read_bytes()).hexdigest()
def freeze(p,name):
 d=p.read_bytes(); h=hashlib.sha256(d).hexdigest(); q=O/'inputs'/name;q.parent.mkdir(exist_ok=True);q.write_bytes(d)
 assert sha(p)==h==sha(q)
 rows.append(dict(original=str(p),copy=str(q),sha256=h));return q
rows=[]
spec=[('sol-fresh-source-discovery-r214','tyszka'),('sol-fresh-source-discovery-r214','tyszka-later'),('sol-fresh-source-discovery-r214','akman'),('sol-wide-structural-analytic-scout-r216','0912.1018v1'),('sol-veto-core-breadth-depth-r1','2608.17863'),('sol-veto-core-breadth-depth-r1','2502.10068')]
for lane,key in spec:
 p=B/lane/'sources'/(key+'.pdf'); q=freeze(p,key+'.pdf'); w=O/'work';w.mkdir(exist_ok=True);r=w/q.name;r.write_bytes(q.read_bytes());assert sha(q)==sha(r)
 subprocess.run(['pdftotext','-layout',str(r),str(w/(key+'.txt'))],check=True)
for lane in ['sol-fresh-source-discovery-r214','sol-wide-structural-analytic-scout-r216','sol-veto-core-breadth-depth-r1']:
 for n in ['http.jsonl','source-versions.json','versions.json']:
  p=B/lane/n
  if p.exists():freeze(p,lane+'-'+n)
p=B/'sol-fresh-source-discovery-r212/qualified-original-index.json';q=freeze(p,'history-index.json')
(O/'body-bindings.json').write_text(json.dumps(rows,indent=2))
print('history index schema',q.read_text()[:2200])
for key in ['tyszka','tyszka-later','0912.1018v1','2608.17863']:
 t=(O/'work'/(key+'.txt')).read_text(); print('\nBODY',key)
 if key=='tyszka':print(t[t.find('Conjecture 3.'):t.find('Conjecture 3.')+3000]); print(t[t.find('Conjecture 5.'):t.find('Conjecture 5.')+4300])
 elif key=='tyszka-later':print(t[:9000])
 elif key=='0912.1018v1': print(t[t.find('Theorem 3.1'):t.find('Theorem 3.1')+16000])
 else: print(t[-22000:])
