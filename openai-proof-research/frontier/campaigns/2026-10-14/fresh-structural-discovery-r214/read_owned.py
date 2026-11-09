from pathlib import Path
import sys,json,hashlib
R=Path("frontier/campaigns/2026-10-14/fresh-structural-discovery-r214")
name=sys.argv[1];a=int(sys.argv[2]);z=int(sys.argv[3]);p=R/"private/source/build"/name
b=p.read_bytes(); assert 0<=a<z<=len(b)
s=b[a:z].decode("utf-8")
rec={"file":str(p.relative_to(R)),"start":a,"stop":z,"total":len(b),"sha256":hashlib.sha256(b).hexdigest(),"type":"requested full semantic display; tool truncation must be assessed separately"}
with (R/"private/read-extents.jsonl").open("a") as f:f.write(json.dumps(rec)+"\n")
print(json.dumps(rec));print(s)
