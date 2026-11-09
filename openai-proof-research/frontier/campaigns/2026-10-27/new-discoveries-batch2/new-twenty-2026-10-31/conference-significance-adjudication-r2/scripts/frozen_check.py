import json,hashlib,sys
d=json.load(open(sys.argv[1]));ok=0;bad=[]
for p,h in d.items():
    try: g=hashlib.sha256(open(p,'rb').read()).hexdigest()
    except Exception as e: bad.append((p,str(e)));continue
    if g==h: ok+=1
    else: bad.append((p,g))
print(json.dumps({"total":len(d),"match":ok,"mismatch":bad},indent=1))
