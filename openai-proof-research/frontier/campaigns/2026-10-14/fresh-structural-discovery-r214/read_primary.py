from pathlib import Path
import sys,json,hashlib
R=Path("frontier/campaigns/2026-10-14/fresh-structural-discovery-r214")
name=sys.argv[1];a=int(sys.argv[2]);z=int(sys.argv[3]); selections=json.loads((R/"private/primary/selections.json").read_text())
assert any(x[0]<=a<z<=x[1] for x in selections[name]),"outside selected mathematical interval"
p=R/"private/primary"/(name+".txt");b=p.read_bytes();s=b[a:z].decode()
rec={"name":name,"start":a,"stop":z,"total":len(b),"sha256":hashlib.sha256(b).hexdigest(),"type":"semantic display; PDF formula fidelity separately limited"}
with (R/"private/primary/read-extents.jsonl").open("a") as f:f.write(json.dumps(rec)+"\n")
print(json.dumps(rec));print(s)
