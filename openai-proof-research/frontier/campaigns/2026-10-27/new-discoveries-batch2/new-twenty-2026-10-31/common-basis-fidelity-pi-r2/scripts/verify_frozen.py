import json, hashlib, sys, os
LANE=os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
fz=json.load(open(os.path.join(LANE,'frozen-inputs.json')))
print('entries:',len(fz)); bad=[];missing=[]
for path,meta in fz.items():
    exp=meta['sha256'] if isinstance(meta,dict) else meta
    if not os.path.exists(path): missing.append(path); continue
    h=hashlib.sha256(open(path,'rb').read()).hexdigest()
    if h!=exp: bad.append((path,exp,h))
print('missing:',len(missing)); print('mismatched:',len(bad))
for b in bad[:20]: print(b)
json.dump({'entries':len(fz),'missing':missing,'mismatched':bad},open(os.path.join(LANE,'logs','frozen-verify-pass1.json'),'w'),indent=1)
