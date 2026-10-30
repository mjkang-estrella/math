import json,gzip,re,hashlib
from pathlib import Path
L=Path(__file__).resolve().parent
pat=re.compile(r'McDermott|2606[.]25250|375559|stable.quadratic|demark|eventual.stability|gaussian.*(iterat|recurr|quadratic)|quadratic.*(stabil|gaussian)',re.I)
records=[]
for rel in ['sol-fresh-source-discovery-r148/sources/omega-problems-fixed.json','root-edge-irregulator-final-freeze-r1/omega-tree.txt.gz','root-edge-irregulator-final-freeze-r1/openai-tree.txt.gz','sol-fresh-source-discovery-r138/sources/omega-compare.json','sol-fresh-source-discovery-r141/registry-delta.json']:
 p=L.parent/rel;b=p.read_bytes();s=gzip.decompress(b).decode() if p.suffix=='.gz' else b.decode()
 if p.suffix=='.json':
  j=json.loads(s);paths=[x.get('path',x.get('filename','')) for x in j.get('tree',j.get('files',[]))]
 else:paths=[x.split('\t')[-1] for x in s.splitlines()]
 hits=[x for x in paths if pat.search(x)]
 records.append(dict(path=str(p),sha256=hashlib.sha256(b).hexdigest(),hits=hits))
(L/'registry-screen.json').write_text(json.dumps(dict(records=records,omega='490f6bccbf445ab8e111a16b0b8670a5dd7c9a9c',openai='7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a',gaps=['aa026->a19a capped300','a19a->490f capped300','lexical returned paths only; not global semantic clearance']),indent=2)+'\n')
print(json.dumps(records,indent=2))
