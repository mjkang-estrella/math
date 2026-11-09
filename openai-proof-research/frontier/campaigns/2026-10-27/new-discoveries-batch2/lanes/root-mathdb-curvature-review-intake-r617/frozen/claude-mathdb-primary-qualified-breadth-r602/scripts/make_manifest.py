# Write manifest.json covering every lane file except manifest.json itself and final-receipt.json.
import hashlib,json,os,sys
ME=os.path.realpath(sys.argv[1]); EXC=['final-receipt.json','manifest.json']
fs=[]
for r,ds,files in os.walk(ME):
    for f in files:
        p=os.path.relpath(os.path.join(r,f),ME)
        if p in EXC: continue
        b=open(os.path.join(ME,p),'rb').read(); fs.append({'path':p,'sha256':hashlib.sha256(b).hexdigest(),'size':len(b)})
json.dump({'lane':'claude-mathdb-primary-qualified-breadth-r602','excluded_exact_paths':EXC,'files':sorted(fs,key=lambda e:e['path'])},open(os.path.join(ME,'manifest.json'),'w'),indent=1,sort_keys=True)
print(len(fs))
