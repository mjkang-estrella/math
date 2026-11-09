from pathlib import Path
import sys,json,hashlib
R=Path('frontier/campaigns/2026-10-14/fresh-structural-discovery-r217')
p=R/sys.argv[1];a=int(sys.argv[2]);z=int(sys.argv[3]);b=p.read_bytes();ls=[x.encode() for x in b.decode().splitlines(keepends=True)];z=min(z,len(ls));s=b''.join(ls[a-1:z]);assert len(s)<=33000
print(f'{p.relative_to(R)} L{a}-{z} bytes [{sum(map(len,ls[:a-1]))},{sum(map(len,ls[:z]))}) of {len(b)}');print(s.decode())
with (R/'private/semantic-reads.jsonl').open('a') as f:f.write(json.dumps({'path':str(p.relative_to(R)),'lines':[a,z],'bytes':[sum(map(len,ls[:a-1])),sum(map(len,ls[:z]))],'sha256':hashlib.sha256(s).hexdigest(),'mode':'direct selected complete lines; primary formulas subject to text extraction limits'})+'\n')
