import json,hashlib,sys,os
d=json.load(open(sys.argv[1]))
ok=bad=miss=0; bads=[]
for p,h in d['files'].items():
    if not os.path.exists(p): miss+=1; bads.append(('MISSING',p)); continue
    hh=hashlib.sha256(open(p,'rb').read()).hexdigest()
    if hh==h: ok+=1
    else: bad+=1; bads.append(('MISMATCH',p))
print(json.dumps({'total':len(d['files']),'ok':ok,'mismatch':bad,'missing':miss,'bad':bads[:50]},indent=1))
