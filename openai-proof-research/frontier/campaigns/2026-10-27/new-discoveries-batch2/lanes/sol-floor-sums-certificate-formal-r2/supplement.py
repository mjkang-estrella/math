import pathlib,hashlib,json
L=pathlib.Path(__file__).resolve().parent
B=L.parent.parent
rows=json.loads((L/'freeze.json').read_text());seen={r['original'] for r in rows}
paths=[]
for lane in ['sol-floor-sums-source-formal-r1','sol-floor-sums-certificate-r2','sol-floor-sums-certificate-preliminary-review-r1','sol-floor-sums-source-prior-review-r2']:
 paths+=list((B/'lanes'/lane).glob('*.log'))
for parent in B.parents:
 p=parent/'AGENTS.md'
 if p.is_file():paths.append(p)
for p in paths:
 if str(p) in seen:continue
 data=p.read_bytes();h=hashlib.sha256(data).hexdigest()
 q=L/('administrative/ancestors/'+str(len(rows))+'.md' if p.name=='AGENTS.md' else 'frozen/lanes/'+p.parent.name+'/'+p.name)
 q.parent.mkdir(parents=True,exist_ok=True);q.write_bytes(data)
 assert hashlib.sha256(p.read_bytes()).hexdigest()==h==hashlib.sha256(q.read_bytes()).hexdigest()
 rows.append(dict(original=str(p),copy=str(q.relative_to(L)),sha256=h,size=len(data)))
(L/'freeze.json').write_text(json.dumps(rows,indent=2)+'\n');print('frozen files',len(rows))
