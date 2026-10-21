from pathlib import Path
import sys,json,hashlib
r=Path(__file__).resolve().parent
f=sys.argv[1]; start=int(sys.argv[2]); end=int(sys.argv[3]); p=r/"private"/f
b=p.read_bytes(); lines=b.decode().splitlines(); selected=lines[start-1:end]
print(f"FILE {f} L{start}-{min(end,len(lines))} / {len(lines)}")
for i,line in enumerate(selected,start): print(f"{i}: {line}")
with (r/"private/READ-LOG.jsonl").open("a") as out: out.write(json.dumps({"path":f,"start":start,"end":min(end,len(lines)),"sha256":hashlib.sha256(b).hexdigest(),"meaning":"requested display; truncation corrections recorded in limits"})+"\n")
