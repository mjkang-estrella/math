from pathlib import Path
import sys,json,hashlib
R=Path(__file__).resolve().parents[3]
S=R/'frontier/sources/i157_dimension_independent_oracle_tolerance_r2'
assert not (S/'seal.json').exists()
p=sys.argv[1];a=int(sys.argv[2]);b=(R/p).read_bytes();ls=b.decode().splitlines();z=int(sys.argv[3]) if len(sys.argv)>3 else len(ls)
assert 1<=a<=z<=len(ls)
rec=dict(path=p,start=a,end=z,lines=len(ls),sha256=hashlib.sha256(b).hexdigest(),passage_sha256=hashlib.sha256('\n'.join(ls[a-1:z]).encode()).hexdigest(),ending=ls[z-1],convention='UTF-8 splitlines, LF join, no appended LF',status='displayed; truncation exceptions recorded separately')
f=S/'read-log.json';log=json.loads(f.read_text()) if f.exists() else [];log.append(rec);f.write_text(json.dumps(log,indent=2)+'\n')
print(json.dumps(rec));print('\n'.join(f'{i+1}: {ls[i]}' for i in range(a-1,z)))
