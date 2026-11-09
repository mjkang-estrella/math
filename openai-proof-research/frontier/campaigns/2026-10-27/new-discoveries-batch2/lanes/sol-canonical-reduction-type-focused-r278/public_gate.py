from pathlib import Path
import hashlib,json,re
L=Path(__file__).resolve().parent;R=L.parent.parent.parents[3]
refs=json.loads((L/'source-bindings.json').read_text());results=[]
def read(p):
 b=p.read_bytes();h=hashlib.sha256(b).hexdigest();refs.append(dict(path=str(p),sha256=h,immutable_reference=True));return b.decode(errors='replace')
for n in ['upstream.json','CONTENTS.md','preprints-tree.json']:
 s=read(R/'sources'/n)
 matches=[line for line in s.splitlines() if re.search(r'canonical|Moscariello|semigroup|pseudo.Frobenius',line,re.I)]
 results.append(dict(path=str(R/'sources'/n),matches=matches[:30]))
total=0;scanned=0;skipped=0
paths=sorted((R/'sources'/'cache').rglob('*'))
paths += sorted((L.parent/'sol-fresh-analytic-focused-resolution-r275'/'sources').glob('Problems--*.md'))
for p in paths:
 if not p.is_file() or p.suffix not in ['.md','.tex','.lean','.json','.txt']:continue
 size=p.stat().st_size
 if size>500000 or total+size>32000000:skipped+=1;continue
 s=read(p);total+=size;scanned+=1
 matches=[s[max(0,m.start()-150):m.end()+500] for m in re.finditer(r'canonical.{0,30}reduction|Moscariello|2003\.05391|pseudo.Frobenius',s,re.I)]
 if matches:results.append(dict(path=str(p),matches=matches[:10]))
history=json.loads((L/'history-semantic.json').read_text())
print('History matching reports:',[Path(v['path']).parent.name+'/'+Path(v['path']).name for v in history])
out=dict(cached_bodies_scanned=scanned,bytes=total,skipped=skipped,index_and_body_matches=results,current_registry_head='UNKNOWN; prohibited denied routes not retried; cached coverage is not clearance')
(L/'public-semantic-gate.json').write_text(json.dumps(out,indent=2));(L/'source-bindings.json').write_text(json.dumps(refs,indent=2))
print(json.dumps(out,indent=2)[:8000])
for p in [L/'admin'/'ledger.json',L/'admin'/'prior-campaign-context.json']:
 j=json.loads(p.read_text());print(p.name,'top-level keys',list(j),'all JSON parsed; counts',[(k,j[k]) for k in ['accepted_count','total_accepted_count','next_global_outcome_number'] if k in j])
