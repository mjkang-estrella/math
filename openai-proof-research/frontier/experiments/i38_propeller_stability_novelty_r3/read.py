import sys,re,json,hashlib
from pathlib import Path
R=Path(__file__).resolve().parents[3];S=R/'frontier/sources/i38_propeller_stability_novelty_r3';p=R/sys.argv[1];raw=p.read_bytes();a=raw.splitlines(keepends=True);lo=int(sys.argv[2]) if len(sys.argv)>2 else 1;hi=int(sys.argv[3]) if len(sys.argv)>3 else len(a)
print(str(p.relative_to(R))+f' lines {lo}-{hi} / {len(a)}')
for i,line in enumerate(a[lo-1:hi],lo):print(f'{i}: '+re.sub(' +',' ',line.decode(errors='replace').rstrip()))
f=S/'read-log.json';v=json.loads(f.read_text()) if f.exists() else [];v.append({'path':str(p.relative_to(R)),'sha256':hashlib.sha256(raw).hexdigest(),'start':lo,'end':min(hi,len(a)),'passage_sha256':hashlib.sha256(b''.join(a[lo-1:hi])).hexdigest()});f.write_text(json.dumps(v,indent=2)+'\n')
