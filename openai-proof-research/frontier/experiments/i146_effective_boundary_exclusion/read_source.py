import sys,json,hashlib
from pathlib import Path
p=Path(sys.argv[1]);offset=int(sys.argv[2]);ls=p.read_text().splitlines();end=offset;size=0
while end<len(ls) and (size+len(ls[end])<16000 or end==offset):size+=len(ls[end])+1;end+=1
b=p.read_bytes();chunk="\n".join(ls[offset:end]);r=dict(path=str(p),sha256=hashlib.sha256(b).hexdigest(),bytes=len(b),start=offset+1,end=end,total_lines=len(ls),ending=ls[end-1],passage_sha256=hashlib.sha256(chunk.encode()).hexdigest())
with Path("frontier/sources/i146_effective_boundary_exclusion/read-log.jsonl").open("a") as f:f.write(json.dumps(r)+"\n")
print(f"LINES {offset+1}-{end}/{len(ls)} NEXT {end}\n"+chunk)
