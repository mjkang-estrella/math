from pathlib import Path
import sys,json,hashlib
ROOT=Path("frontier/campaigns/2026-10-14/fresh-structural-discovery-r219/packet")
p=ROOT/sys.argv[1]
b=p.read_bytes(); lines=b.splitlines(keepends=True)
a,z=map(int,sys.argv[2:4]); z=z or len(lines); assert 1<=a<=z<=len(lines)
lo=sum(map(len,lines[:a-1]));hi=sum(map(len,lines[:z]));selection=b[lo:hi]
print(f"{sys.argv[1]} lines {a}..{z}, bytes [{lo},{hi}), file bytes {len(b)}")
print(selection.decode())
with (ROOT/"private/reads.jsonl").open("a") as f:
 f.write(json.dumps({"file":sys.argv[1],"line_first":a,"line_last":z,"byte_first":lo,"byte_stop":hi,"selection_sha256":hashlib.sha256(selection).hexdigest(),"parser":"bytes.splitlines(keepends=True)"})+"\n")
