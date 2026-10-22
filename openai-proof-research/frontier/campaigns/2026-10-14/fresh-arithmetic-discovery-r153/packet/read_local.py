from pathlib import Path
import sys,json
r=Path(__file__).parent
p=r/sys.argv[1]
b=p.read_bytes();a=int(sys.argv[2]) if len(sys.argv)>2 else 0;z=int(sys.argv[3]) if len(sys.argv)>3 else len(b)
# Line boundaries selected forward, preserving exact UTF8 characters.
if a and b[a-1:a]!=b"\n":a=b.index(b"\n",a)+1
if z<len(b) and b[z-1:z]!=b"\n":z=b.index(b"\n",z)+1
print(str(p),f"[{a},{z}) / {len(b)}")
print(b[a:z].decode())
with (r/"private/display-extents.jsonl").open("a") as f:f.write(json.dumps({"path":str(p.relative_to(r)),"start":a,"end":z,"note":"requested display; semantic coverage qualified by reading record"})+"\n")
