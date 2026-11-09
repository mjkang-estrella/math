# Write manifest.json covering every lane file except exactly manifest.json and final-receipt.json.
import os,sys,json,hashlib
O=os.path.abspath(sys.argv[1]);EX={'manifest.json','final-receipt.json'};fl=[]
for r,ds,fs in os.walk(O):
    for f in fs:
        rel=os.path.relpath(os.path.join(r,f),O)
        if rel in EX: continue
        b=open(os.path.join(r,f),'rb').read();fl.append(dict(path=rel,sha256=hashlib.sha256(b).hexdigest(),size=len(b)))
fl.sort(key=lambda x:x['path'])
json.dump(dict(lane=os.path.basename(O),excluded_exact=sorted(EX),files=fl),open(os.path.join(O,'manifest.json'),'w'),indent=1)
print(len(fl))
