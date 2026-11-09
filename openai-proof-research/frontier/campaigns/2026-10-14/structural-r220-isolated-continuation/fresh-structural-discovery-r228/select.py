from pathlib import Path
import json,hashlib,sys
ROOT=Path("frontier/campaigns/2026-10-14/structural-r220-isolated-continuation/fresh-structural-discovery-r228")
def show(rel,start=1,end=None,skip=()):
 p=ROOT/rel; b=p.read_bytes(); lines=b.splitlines(keepends=True); end=end or len(lines)
 assert 1<=start<=end<=len(lines)
 lo=sum(map(len,lines[:start-1])); hi=sum(map(len,lines[:end])); assert b[lo:hi]==b"".join(lines[start-1:end])
 print("\nSELECT",rel,"lines",start,end,"bytes",lo,hi)
 for i in range(start,end+1):
  if i not in skip:print(f"{i}: "+lines[i-1].decode("utf-8").rstrip("\r\n"))
  else:print(f"{i}: [MASKED editorial/production; not proof coverage]")
 rec={"file":rel,"lines_inclusive":[start,end],"bytes_half_open":[lo,hi],"masked_lines":list(skip),"sha256":hashlib.sha256(b).hexdigest()}
 with (ROOT/"private/semantic-reads.jsonl").open("a") as f:f.write(json.dumps(rec)+"\n")
if __name__=="__main__":
 show(sys.argv[1],int(sys.argv[2]) if len(sys.argv)>2 else 1,int(sys.argv[3]) if len(sys.argv)>3 else None)
