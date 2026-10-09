from pathlib import Path
import json,hashlib,datetime,sys,shutil
R=Path(__file__).resolve().parents[3]
S=R/'frontier/sources/i30_einstein_metric_stability_novelty_r3'
E=R/'frontier/experiments/i30_einstein_metric_stability_novelty_r3'
def digest(b): return hashlib.sha256(b).hexdigest()
def row(p):
 b=p.read_bytes(); return dict(path=str(p.relative_to(R)),sha256=digest(b),bytes=len(b))
def dump(p,o): p.write_text(json.dumps(o,indent=2,ensure_ascii=False)+'\n')
if sys.argv[1]=='freeze':
 names=['AGENTS.md','frontier/TEN-FINDINGS.md','sources/upstream.json','frontier/iterations/iteration30-einstein-metric-stability-novelty-r3-task.json','frontier/iterations/iteration30-einstein-metric-stability-task.json','frontier/iterations/iteration30-einstein-metric-stability-r2-task.json','frontier/iterations/iteration27-geometric-analysis-discovery-task.json','frontier/iterations/i27-geometric-analysis-discovery.md','frontier/iterations/i30-einstein-metric-stability.md','frontier/reviews/i30-einstein-metric-stability-r2.md','frontier/sources/i30-parent-preliminary-review.md','frontier/experiments/i30-parent-verification.json','frontier/experiments/i30-proof-r2-parent-verification.json']
 rows=[]
 for n in names:
  p=R/n; dest=S/'frozen'/n; dest.parent.mkdir(parents=True,exist_ok=True); shutil.copyfile(p,dest)
  rows.append(dict(**row(p),frozen=str(dest.relative_to(R)),shared=n=='frontier/TEN-FINDINGS.md'))
 dump(S/'input-manifest.json',dict(time=datetime.datetime.now(datetime.timezone.utc).isoformat(),files=rows))
 task=json.loads((R/names[3]).read_text()); (S/'review-brief.txt').write_text(task['brief']+'\n')
 deps=set()
 for prefix in ['i30_einstein_metric_stability','i30_einstein_metric_stability_r2']:
  base=R/'frontier/sources'/prefix
  for x in json.loads((base/'artifact-seal.json').read_text())['files']: deps.add(x['path'])
  deps.add(str((base/'artifact-seal.json').relative_to(R)))
 for x in json.loads((R/'frontier/sources/i30_einstein_metric_stability/source-manifest.json').read_text())['files']: deps.add(x['local'])
 deps.update(['sources/CONTENTS.md','sources/preprints-tree.json','frontier/sources/i14_spectral_width_novelty_r3/corpus-manifest.json'])
 dump(S/'dependency-manifest.json',dict(files=[row(R/n) for n in sorted(deps)]))
 print('Frozen',len(rows),'inputs;',len(deps),'read-only dependencies')
elif sys.argv[1]=='read':
 name,start,end,purpose=sys.argv[2],int(sys.argv[3]),int(sys.argv[4]),sys.argv[5]
 p=R/name; lines=p.read_bytes().splitlines(keepends=True); end=min(end,len(lines)) if end else len(lines)
 frag=b''.join(lines[start-1:end]); mf=S/'read-passages.json'; data=json.loads(mf.read_text()) if mf.exists() else []
 item=dict(path=name,start=start,end=end,file_sha256=digest(p.read_bytes()),sha256=digest(frag),purpose=purpose)
 if item not in data: data.append(item)
 dump(mf,data)
 print(f'{name} lines {start}-{end}\n'+frag.decode(errors='replace'))
