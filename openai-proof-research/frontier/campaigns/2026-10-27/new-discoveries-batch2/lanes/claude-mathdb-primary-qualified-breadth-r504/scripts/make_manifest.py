import hashlib,json,os,sys
L=os.path.realpath(sys.argv[1]); EX={'manifest.json','final-receipt.json'}; fs=[]
for r,ds,files in os.walk(L):
    for f in files:
        p=os.path.relpath(os.path.join(r,f),L)
        if p in EX: continue
        b=open(os.path.join(L,p),'rb').read(); fs.append({'path':p,'sha256':hashlib.sha256(b).hexdigest(),'size':len(b)})
fs.sort(key=lambda e:e['path'])
with open(os.path.join(L,'manifest.json'),'w',encoding='utf-8') as f: json.dump({'excluded_exact_paths':sorted(EX),'files':fs},f,indent=1); f.write('\n')
print(len(fs))
