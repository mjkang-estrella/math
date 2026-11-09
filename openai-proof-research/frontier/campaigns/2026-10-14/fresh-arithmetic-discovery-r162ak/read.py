from pathlib import Path
import sys,json
root=Path(__file__).resolve().parent
p=root/sys.argv[1]
a,b=map(int,sys.argv[2:4]); data=p.read_bytes(); lines=data.split(b"\n"); start=sum(len(x)+1 for x in lines[:a-1]); end=min(len(data),sum(len(x)+1 for x in lines[:b]))
for i in range(a-1,min(b,len(lines))): print(f"{i+1}: "+lines[i].decode())
with (root/"private/reads.jsonl").open("a") as f: f.write(json.dumps(dict(path=sys.argv[1],start=start,end=end,lines=[a,min(b,len(lines))]))+"\n")
