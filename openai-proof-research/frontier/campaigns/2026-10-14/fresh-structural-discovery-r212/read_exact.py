import sys,json,hashlib
from pathlib import Path
R=Path("frontier/campaigns/2026-10-14/fresh-structural-discovery-r212")
folders={"S":"Spectral-scalar-curvature-and-uniform-Urysohn-width-October-5-2026","T":"Spectral-scalar-curvature-and-Urysohn-width-in-dimension-three-October-5-2026","P":"Positive-scalar-curvature-and-uniform-codimension-two-width-September-23-2026"}
for spec in sys.argv[1:]:
 alias,rel,a,b=spec.split(":");f=R/"private/upstream/preprints"/folders[alias]/rel
 raw=f.read_bytes();a=int(a);b=len(raw) if b=="end" else int(b);assert 0<=a<b<=len(raw)
 chunk=raw[a:b];text=chunk.decode("utf-8")
 print(f"\n=== {alias}/{rel} EXACT BYTES [{a},{b})/{len(raw)} ===\n{text}")
 with (R/"private/read-extents.jsonl").open("a") as out:out.write(json.dumps({"path":str(f.relative_to(R)),"start":a,"end":b,"total":len(raw),"sha256":hashlib.sha256(raw).hexdigest(),"kind":"displayed source bytes; semantic reading performed by research agent; tool truncations separately recovered"})+"\n")
