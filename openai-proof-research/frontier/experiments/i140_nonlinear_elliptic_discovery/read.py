from pathlib import Path
import sys,json,hashlib
R=Path(__file__).resolve().parents[3];S=R/'frontier/sources/i140_nonlinear_elliptic_discovery'
p=sys.argv[1]
if p.isdigit():p=next(d['decoded'] for d in json.loads((S/'context-manifest.json').read_text()) if '/iteration'+p+'-' in d['path'])
b=(R/p).read_bytes();ls=b.decode().splitlines();st=int(sys.argv[2]) if len(sys.argv)>2 else 1;en=int(sys.argv[3]) if len(sys.argv)>3 else len(ls);assert 1<=st<=en<=len(ls)
t='\n'.join(ls[st-1:en]);assert len(t)<50000,('split read',len(t))
r={'path':p,'sha256':hashlib.sha256(b).hexdigest(),'bytes':len(b),'start':st,'end':en,'total_lines':len(ls),'passage_sha256':hashlib.sha256(t.encode()).hexdigest(),'ending':ls[en-1],'convention':'UTF-8 splitlines; joined LF; no appended LF'}
with (S/'reads.jsonl').open('a') as f:f.write(json.dumps(r,ensure_ascii=False)+'\n')
print(p,st,en,len(ls));print(t)
