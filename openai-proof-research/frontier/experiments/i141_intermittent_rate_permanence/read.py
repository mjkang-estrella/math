import sys,json,hashlib
from pathlib import Path
assert not Path('frontier/sources/i141_intermittent_rate_permanence/seal.json').exists(),'Reading log frozen after seal'
p=Path(sys.argv[1]);b=p.read_bytes();t=b.decode();a=int(sys.argv[2]) if len(sys.argv)>2 else 0;z=min(int(sys.argv[3]),len(t)) if len(sys.argv)>3 else len(t);out=t[a:z]
r=dict(path=str(p),sha256=hashlib.sha256(b).hexdigest(),char_start=a,char_end=z,total_characters=len(t),start_line=t[:a].count(chr(10))+1,end_line=t[:z].count(chr(10))+1,raw_lf=b.count(b"\n"),splitlines=len(t.splitlines()),terminal_lf=b.endswith(b"\n"),ending=out[-160:],range_sha256=hashlib.sha256(out.encode()).hexdigest(),display_status="supplied")
f=Path("frontier/sources/i141_intermittent_rate_permanence/read-manifest.json");v=json.loads(f.read_bytes()) if f.exists() else [];v.append(r);f.write_text(json.dumps(v,indent=2)+"\n");print(json.dumps(r));print(out)
