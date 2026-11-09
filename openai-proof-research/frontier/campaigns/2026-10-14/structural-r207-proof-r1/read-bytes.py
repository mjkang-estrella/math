import sys,json,hashlib
from pathlib import Path
A=Path("frontier/campaigns/2026-10-14/fresh-structural-discovery-r207");R=Path("frontier/campaigns/2026-10-14/structural-r207-proof-r1")
M=json.loads((A/"MANIFEST.json").read_text());rel=sys.argv[1];lo=int(sys.argv[2]);hi=int(sys.argv[3]);assert rel in M["files"]
allowed={"dkrrz":[(0,25295),(34691,42529)],"baudier":[(0,17787)],"kw":[(0,17440)],"diamonds":[(127175,144366)],"bartlett":[(14143,20529)],"levina":[(17530,22200)],"johnson":[(6000,16000)]}
assert rel.startswith("private/primary/") and rel.endswith(".txt");key=Path(rel).stem;assert any(a<=lo<hi<=b for a,b in allowed[key])
b=(A/"packet"/rel).read_bytes();assert hashlib.sha256(b).hexdigest()==M["files"][rel]["sha256"]
print(f"FILE {rel} bytes [{lo},{hi})/{len(b)}\n"+b[lo:hi].decode())
with (R/"packet/private/read-log.jsonl").open("a") as f:f.write(json.dumps({"path":rel,"bytes":[lo,hi],"total_bytes":len(b),"sha256":hashlib.sha256(b).hexdigest(),"kind":"primary body displayed within disclosed selected extent"})+"\n")
