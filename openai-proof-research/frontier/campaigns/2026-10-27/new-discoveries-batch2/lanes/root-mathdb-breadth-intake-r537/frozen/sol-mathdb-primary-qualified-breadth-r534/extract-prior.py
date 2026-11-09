from extract import P,D
import json,hashlib
x=json.loads((D/'prior-retrieval-bindings.json').read_text());b=(D/x['path']).read_bytes();assert hashlib.sha256(b).hexdigest()==x['sha256'] and len(b)==x['size'];h=P();h.feed(b.decode());p=D/'2412.05857v1.txt';p.write_text(''.join(h.x));b=p.read_bytes();(D/'prior-derivative-binding.json').write_text(json.dumps(dict(path=p.name,size=len(b),sha256=hashlib.sha256(b).hexdigest()),indent=2)+'\n')
