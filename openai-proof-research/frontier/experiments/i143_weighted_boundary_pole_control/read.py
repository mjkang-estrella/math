"""Development-only passage recorder; never loaded by offline verifier."""
from pathlib import Path
assert not Path("frontier/sources/i143_weighted_boundary_pole_control/seal.json").exists(), "sealed reading record cannot be changed"
import json,hashlib,sys
p=Path(sys.argv[1]);a=int(sys.argv[2]);b=int(sys.argv[3]);raw=p.read_bytes();ls=raw.decode().splitlines();assert 1<=a<=b<=len(ls)
r=dict(path=str(p),sha256=hashlib.sha256(raw).hexdigest(),bytes=len(raw),start=a,end=b,total_lines=len(ls),ending=ls[b-1],passage_sha256=hashlib.sha256('\n'.join(ls[a-1:b]).encode()).hexdigest())
f=Path('frontier/sources/i143_weighted_boundary_pole_control/read-manifest.json');d=json.loads(f.read_text());d['passages'].append(r);f.write_text(json.dumps(d,indent=2)+'\n');print(str(p),a,b,'of',len(ls));print('\n'.join(ls[a-1:b]))
