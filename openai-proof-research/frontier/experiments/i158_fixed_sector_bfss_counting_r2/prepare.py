"""Own author preparation; no ancestor execution or corpus copies."""
from pathlib import Path
import hashlib,json,re
S=Path('frontier/sources/i158_fixed_sector_bfss_counting_r2')
A=Path('frontier/sources/i155_fixed_sector_bfss_counting')
assert not (S/'seal.json').exists()
def load(p):return json.loads(Path(p).read_text())
def put(p,x):Path(p).write_text(json.dumps(x,ensure_ascii=False,indent=2)+'\n')
def row(p):
 b=Path(p).read_bytes();return dict(path=str(p),sha256=hashlib.sha256(b).hexdigest(),bytes=len(b))
contexts=load(A/'contexts.json')+[dict(raw='frontier/iterations/iteration155-fixed-sector-bfss-counting-task.json',snapshot='frontier/iterations/iteration155-fixed-sector-bfss-counting-task.json',sha256='e32170f6d05bfcfea861e801830655650dfe8fb3813b893243bf3428dda775e1')]
put(S/'contexts.json',contexts)
base=load(A/'decoded-lines.json');lines=list(base);lookup={s:i for i,s in enumerate(lines)};fields=[]
def ids(s):
 out=[]
 for line in s.splitlines(keepends=True):
  if line not in lookup:lookup[line]=len(lines);lines.append(line)
  out.append(lookup[line])
 return out
def walk(x,p):
 if isinstance(x,dict):
  fields.append(dict(path=p,kind='object',keys=list(x)))
  for k,v in x.items():walk(v,p+[k])
 elif isinstance(x,list):
  fields.append(dict(path=p,kind='array',length=len(x)))
  for i,v in enumerate(x):walk(v,p+[i])
 elif isinstance(x,str):
  try:z=json.loads(x)
  except ValueError:z=None
  if isinstance(z,(dict,list)):
   fields.append(dict(path=p,kind='json-string'));walk(z,p+['<JSON>']);return
  for m in re.finditer(r'(?m)^\{',x):
   try:z=json.loads(x[m.start():])
   except ValueError:continue
   if isinstance(z,dict):
    fields.append(dict(path=p,kind='text-plus-JSON',prefix=ids(x[:m.start()])));walk(z,p+['<parent JSON>']);return
  fields.append(dict(path=p,kind='string',lines=ids(x)))
 else:fields.append(dict(path=p,kind='scalar',value=x))
for c in contexts:walk(load(c['snapshot']),[c['snapshot']])
put(S/'decoded-fields.json',fields)
put(S/'decoded-new-lines.json',lines[len(base):])
(S/'decoded-new-view.txt').write_text(''.join(f'{i}: {s}'+('' if s.endswith('\n') else '\n') for i,s in enumerate(lines[len(base):],len(base))))
sc={}
for f in fields:
 if f['kind']=='scalar':
  k=json.dumps([f['path'][-1],f['value']],ensure_ascii=False);sc.setdefault(k,[]).append(f['path'])
put(S/'scalar-occurrences.json',sc)
(S/'scalar-view.txt').write_text(''.join(k+'\n' for k in sc))
refs={r['path']:r for r in load(A/'references.json')}
for r in load(A/'seal.json')['files']+[row(A/'seal.json')]+[row(c['raw']) for c in contexts]+[row('frontier/experiments/i155-parent-verification.json')]:
 refs[r['path']]=r
for r in refs.values():assert not re.search(r'(?:^|/)(?:i|iteration)(?:156|157)(?:[-_/])',r['path'])
put(S/'references.json',sorted(refs.values(),key=lambda r:r['path']))
packs=load(A/'inherited-packages.json')+[dict(source=str(A),experiment='frontier/experiments/i155_fixed_sector_bfss_counting',report='frontier/iterations/i155-fixed-sector-bfss-counting.md',seal=row(A/'seal.json'))]
put(S/'inherited-packages.json',packs)
put(S/'decode-reuse.json',dict(base_lines=row(A/'decoded-lines.json'),base_view=row(A/'decoded-view.txt'),base_count=len(base),total_lines=len(lines),field_occurrences=len(fields),scope='Occurrences and exact string line references retained. Byte extraction is not semantic reading.'))
print(json.dumps(dict(contexts=len(contexts),base_lines=len(base),new_lines=len(lines)-len(base),new_characters=sum(map(len,lines[len(base):])),fields=len(fields))))
