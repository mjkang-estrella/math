from pathlib import Path
import json,hashlib
R=Path(__file__).parent

def show(path,start,end,note="semantic read"):
 p=R/path;b=p.read_bytes();ls=b.splitlines(keepends=True);assert 1<=start<=end<=len(ls)
 a=sum(map(len,ls[:start-1]));z=sum(map(len,ls[:end]));part=b[a:z];assert part==b"".join(ls[start-1:end])
 print(f"\nREAD {path} lines {start}-{end}, bytes [{a},{z})\n"+part.decode())
 with (R/"private/read-extents.jsonl").open("a") as f:f.write(json.dumps({"path":path,"lines":[start,end],"bytes":[a,z],"sha256":hashlib.sha256(part).hexdigest(),"note":note})+"\n")
