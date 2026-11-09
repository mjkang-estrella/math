import sys,json,hashlib
from pathlib import Path
R=Path("frontier/campaigns/2026-10-14/fresh-structural-discovery-r212")
for spec in sys.argv[1:]:
 name,a,b=spec.split(":");p=R/"private/primary"/(name+".txt");raw=p.read_bytes();a=int(a);b=len(raw) if b=="end" else int(b);assert 0<=a<b<=len(raw)
 print(f"\n=== PRIMARY {name} TEXT BYTES [{a},{b})/{len(raw)} ===\n"+raw[a:b].decode())
 with (R/"private/primary-read-extents.jsonl").open("a") as f:f.write(json.dumps({"name":name,"start":a,"end":b,"total":len(raw),"sha256":hashlib.sha256(raw).hexdigest(),"limits":"PDF-to-text extraction; layout/equations may need original PDF page confirmation; this exact displayed range only"})+"\n")
