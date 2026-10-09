from pathlib import Path
import json,hashlib
R=Path(__file__).resolve().parents[3]; S=R/'frontier/sources/i30_einstein_metric_stability_novelty_r3'
def dump(p,x): p.write_text(json.dumps(x,indent=2,ensure_ascii=False)+'\n')
def row(p):
 b=p.read_bytes();return dict(path=str(p.relative_to(R)),bytes=len(b),sha256=hashlib.sha256(b).hexdigest())
reads=json.loads((S/'read-passages.json').read_text())
for x in reads:
 if 'c1=0 splitting' in x['purpose']:x['purpose']='Additional search hit: exact compatible holomorphic splitting, not metric stability'
dump(S/'read-passages.json',reads)
for i in range(1,6):
 p=S/f'search{i}.json'
 if p.exists():
  try:json.loads(p.read_text())
  except json.JSONDecodeError:p.rename(S/f'search{i}.txt')
manifest=json.loads((R/'frontier/sources/i30_einstein_metric_stability/source-manifest.json').read_text())
selected={x['path']:x for x in manifest['files']}
corpus={x['path']:x for x in json.loads((R/'frontier/sources/i14_spectral_width_novelty_r3/corpus-manifest.json').read_text())['files']}
for x in reads:
 marker='/corpus/'
 if marker in x['path']:
  n=x['path'].split(marker)[1];selected[n]=dict(**corpus[n],local=x['path'])
dump(S/'source-manifest.json',dict(pin=manifest['pin'],files=list(selected.values()),policy='Selected pinned files only; physical files reused read-only. Not all retained files are claimed semantically read.'))
deps=json.loads((S/'dependency-manifest.json').read_text()); names={x['path'] for x in deps['files']}
names.update(x['path'] for x in reads if not x['path'].startswith(str(S.relative_to(R))))
names.update(x['local'] for x in selected.values())
dump(S/'dependency-manifest.json',dict(files=[row(R/n) for n in sorted(names)]))
queries=dict(date='2026-10-09',scope='Six bounded web batches. First five raw response strings retained, without claiming exact query reconstruction. Sixth full request retained verbatim. Primary HTTP requests and UTC retrieval times are exact in new-primary-manifest.json.',batch_topics=['almost-Einstein nonnegative curvature original metric quantitative stability','TW CCL HKRX Ma-Wang strongest published versions','Bamler-Zhang quantitative Einstein Martens Huang-Wang','DSS Bing Wang square-root volume','Clarke L2 metric measurable-subset volume','four exact follow-up queries in search6-request.json'],failed_retrievals='No new primary HTTP failure in this review. Earlier author/R2 publisher 403s remain historical evidence; fresh publisher requests succeeded.',priority_limit='Search engine results are discovery only, not theorem authorities or exhaustive worldwide priority evidence.')
dump(S/'search-record.json',queries)
print('Selected pinned',len(selected),'read-only dependencies',len(names),'opened passage ranges',len(reads))
