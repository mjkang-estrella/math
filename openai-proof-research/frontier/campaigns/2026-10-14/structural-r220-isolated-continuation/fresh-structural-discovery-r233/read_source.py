from pathlib import Path
import sys,json,hashlib
R=Path("frontier/campaigns/2026-10-14/structural-r220-isolated-continuation/fresh-structural-discovery-r233")
name,a,z=sys.argv[1],int(sys.argv[2]),int(sys.argv[3])
p=R/"private-source/build/source"/name
b=p.read_bytes();lines=b.splitlines(keepends=True);offs=[0]
for l in lines:offs.append(offs[-1]+len(l))
assert 1<=a<=z<=len(lines)
masked={37,38,39,40,42} if name=="paper.tex" else set()
print(f"READ {name} lines {a}-{z} bytes [{offs[a-1]},{offs[z]}) of {len(b)}")
for i in range(a-1,z):
 print(f"{i+1}: "+("[production/title wrapper masked]" if i+1 in masked else lines[i].decode().rstrip()))
with (R/"semantic-reads.jsonl").open("a") as f:f.write(json.dumps({"file":str(p.relative_to(R)),"lines":[a,z],"bytes":[offs[a-1],offs[z]],"sha256":hashlib.sha256(b).hexdigest(),"masked_lines":[i for i in sorted(masked) if a<=i<=z],"parser":"bytes.splitlines(keepends=True)"})+"\n")
