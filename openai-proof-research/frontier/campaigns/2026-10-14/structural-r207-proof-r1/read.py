import sys,json,hashlib
from pathlib import Path
A=Path("frontier/campaigns/2026-10-14/fresh-structural-discovery-r207")
R=Path("frontier/campaigns/2026-10-14/structural-r207-proof-r1")
M=json.loads((A/"MANIFEST.json").read_text())
rel=sys.argv[1]
assert rel in M["files"] and rel!="private/history-selected/section-1.txt"
p=A/"packet"/rel;b=p.read_bytes();assert hashlib.sha256(b).hexdigest()==M["files"][rel]["sha256"]
lines=b.decode().splitlines(keepends=True);lo=int(sys.argv[2]) if len(sys.argv)>2 else 1;hi=int(sys.argv[3]) if len(sys.argv)>3 else len(lines);hi=min(hi,len(lines))
start=sum(len(x.encode()) for x in lines[:lo-1]);end=sum(len(x.encode()) for x in lines[:hi])
print(f"FILE {rel} L{lo}-{hi}; bytes [{start},{end})/{len(b)}")
for i in range(lo-1,hi):print(f"{i+1}: {lines[i]}",end="")
with (R/"packet/private/read-log.jsonl").open("a") as f:f.write(json.dumps({"path":rel,"lines":[lo,hi],"bytes":[start,end],"total_bytes":len(b),"sha256":hashlib.sha256(b).hexdigest(),"kind":"body displayed; any output truncation must be recovered"})+"\n")
