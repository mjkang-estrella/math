"""Exact admitted-file semantic reader; source is read only; log stays in review root."""
from pathlib import Path
import argparse,json,hashlib,datetime
ROOT=Path(__file__).resolve().parent
AUTHOR=ROOT.parent/'fresh-structural-discovery-r233'
p=argparse.ArgumentParser();p.add_argument('name');p.add_argument('start',type=int);p.add_argument('end',type=int);a=p.parse_args()
baseline=json.loads((ROOT/'author-baseline.json').read_bytes())
e=next(e for e in baseline['files'] if e['path']==a.name)
b=(AUTHOR/a.name).read_bytes();assert hashlib.sha256(b).hexdigest()==e['sha256']
lines=b.splitlines(keepends=True);assert 1<=a.start<=a.end<=len(lines)
x=sum(map(len,lines[:a.start-1]));y=sum(map(len,lines[:a.end]))
print(f'FILE {a.name} L{a.start}-{a.end} BYTES [{x},{y})')
encoding='latin1' if '/DT12/' in a.name else 'utf-8'
for i in range(a.start-1,a.end):
 line=lines[i].decode(encoding).rstrip('\r\n')
 if a.name.startswith('private-primary/') and line.lstrip().startswith('%'):line='[whole-line TeX comment masked]'
 print(f'{i+1}: '+line)
with (ROOT/'semantic-reads.jsonl').open('a') as f:f.write(json.dumps({'name':a.name,'lines':[a.start,a.end],'bytes':[x,y],'sha256':e['sha256'],'utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'note':'display requested; truncation if any must be recorded separately'})+'\n')
