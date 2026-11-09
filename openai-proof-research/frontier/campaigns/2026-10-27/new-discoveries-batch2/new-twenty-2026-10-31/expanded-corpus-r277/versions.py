exec(compile((__import__('pathlib').Path(__file__).with_name('fetch.py')).read_text().split('records=')[0], 'fetch-prefix', 'exec'))
import re
jobs=[];history={}
for f in sorted((p/'sources').glob('*.abs')):
 a=f.stem;s=f.read_text();vs=sorted(set(re.findall(r'/abs/('+re.escape(a)+r'v\d+)',s)));history[a]=vs
 for v in vs:jobs.append((v,'pdf'))
(p/'version-inventory.json').write_text(json.dumps(history,indent=2))
code=Path(__file__).with_name('fetch.py').read_text();exec(compile(code[code.index('def get(job):'):code.index('with concurrent.futures')], 'get','exec'))
with concurrent.futures.ThreadPoolExecutor(max_workers=4) as pool:out=list(pool.map(get,jobs))
(p/'version-receipts.json').write_text(json.dumps(out,indent=2));print('versions',len(jobs),'errors',[x for x in out if x.get('error')]);print(resource.getrusage(resource.RUSAGE_SELF))
