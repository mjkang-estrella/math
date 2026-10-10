import sys,json,hashlib
from pathlib import Path
ROOT=Path(__file__).resolve().parents[3]
S=ROOT/'frontier/sources/i159_oracle_tolerance_focused_r3'
a=sys.argv[1]; p=ROOT/a
if a.endswith('.tex') and '/' not in a:
 p=ROOT/'frontier/sources/i14_spectral_width_novelty_r3/corpus/preprints/Subpolynomial-query-complexity-for-well-conditioned-log-concave-sampling-September-26-2026/build/sections'/a
b=p.read_bytes(); lines=b.decode().splitlines(); lo=int(sys.argv[2]) if len(sys.argv)>2 else 1; hi=int(sys.argv[3]) if len(sys.argv)>3 else len(lines)
assert 1<=lo<=hi<=len(lines)
part='\n'.join(lines[lo-1:hi]); rec={'path':str(p.relative_to(ROOT)),'sha256':hashlib.sha256(b).hexdigest(),'start':lo,'end':hi,'total_lines':len(lines),'passage_sha256':hashlib.sha256(part.encode()).hexdigest(),'ending':lines[hi-1],'convention':'splitlines then LF join, no appended LF'}
log=S/'read-log.json'; data=json.loads(log.read_text()) if log.exists() else [];data.append(rec);log.write_text(json.dumps(data,indent=2)+'\n')
print(json.dumps(rec)); print('\n'.join(f'{i}: {lines[i-1]}' for i in range(lo,hi+1)))
