from pathlib import Path
import json,itertools,hashlib
L=Path(__file__).resolve().parent
def M(s):
 return sum(s[x-1]==s[y-1]==s[x+y//2-1] for y in range(1,len(s)+1) for x in range(1,len(s)-y//2+1))
def flip(s,F):return ''.join(str(1-int(v)) if i+1 in F else v for i,v in enumerate(s))
s='011001001101';m=M(s);ds=[]
for a in range(1,13):
 for b in range(a,13):ds.append([a,b,M(flip(s,set(range(a,b+1))))-m])
assert m==26 and all(d>0 for a,b,d in ds if (a,b)!=(1,12))
best=(0,None)
for a,b,c,d in itertools.combinations(range(1,14),4):
 F=set(range(a,b))|set(range(c,d));delta=M(flip(s,F))-m
 if delta<best[0]:best=(delta,[a,b-1,c,d-1])
assert best[0]<0
# Check original/copy equality again after scientific reading.
bindings=json.loads((L/'bindings.json').read_text());checked=[]
for r in bindings:
 q=L/r['copy'];assert hashlib.sha256(q.read_bytes()).hexdigest()==r['sha256']
 if r['kind']=='scientific':assert hashlib.sha256(Path(r['original']).read_bytes()).hexdigest()==r['sha256'];checked.append(r['copy'])
# Newly acquired primary bodies remained unchanged after reading.
for path,field,meta in [('2410.21651v1.pdf','sha256','primary-followup.json'),('2410.21651v1.txt','text_sha256','primary-followup.json')]:
 assert hashlib.sha256((L/path).read_bytes()).hexdigest()==json.loads((L/meta).read_text())[field]
ar=json.loads((L/'retrieval.json').read_text())[0];assert hashlib.sha256((L/ar['file']).read_bytes()).hexdigest()==ar['sha256']
out=dict(witness=s,M=m,all_interval_deltas=ds,best_two_interval_exchange=best,scientific_original_copy_checks=len(checked),status='PASS')
(L/'scientific-verification.json').write_text(json.dumps(out,indent=2)+'\n');print(json.dumps({k:v for k,v in out.items() if k!='all_interval_deltas'},indent=2))
