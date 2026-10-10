"""Read-only input extraction; writes receipts only in owned unsealed evidence."""
from pathlib import Path
import json,hashlib,sys
S=Path('frontier/sources/i158_fixed_sector_bfss_counting_r2')
assert not (S/'seal.json').exists()
p=Path(sys.argv[1]);t=p.read_bytes().decode('utf-8')
a=int(sys.argv[2]);b=min(int(sys.argv[3]),len(t));part=t[a:b]
r=dict(path=str(p),sha256=hashlib.sha256(t.encode()).hexdigest(),bytes=len(t.encode()),characters=len(t),start=a,end=b,range_sha256=hashlib.sha256(part.encode()).hexdigest(),ending=part[-160:],raw_lf=t.count('\n'),splitlines=len(t.splitlines()),status='supplied-pending-review')
q=S/'read-manifest.json';rows=json.loads(q.read_text()) if q.exists() else [];rows.append(r);q.write_text(json.dumps(rows,ensure_ascii=False,indent=2)+'\n')
print(json.dumps({'receipt':len(rows)-1,**r},ensure_ascii=False));print(part)
