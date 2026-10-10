"""Development reader. Records requests; completion is asserted only in final read history."""
from pathlib import Path
import sys,json,hashlib
ROOT=Path(__file__).resolve().parents[3]
S=ROOT/'frontier/sources/i134_discrete_geometric_optimization'
p=sys.argv[1];start=int(sys.argv[2]);end=int(sys.argv[3]) if len(sys.argv)>3 else None
b=(ROOT/p).read_bytes();ls=b.decode(errors='replace').splitlines();end=end or len(ls)
assert 1<=start<=end<=len(ls)
out='\n'.join(ls[start-1:end]);h=lambda b:hashlib.sha256(b).hexdigest()
r=dict(path=p,sha256=h(b),bytes=len(b),start=start,end=end,total_lines=len(ls),line_convention='splitlines',passage_sha256=h(out.encode()))
with (S/'read-requests.jsonl').open('a') as f:f.write(json.dumps(r)+'\n')
print(json.dumps(r));print(out)
