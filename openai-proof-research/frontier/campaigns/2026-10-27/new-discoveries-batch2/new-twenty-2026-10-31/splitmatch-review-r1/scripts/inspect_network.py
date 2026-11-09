from pathlib import Path
import json
L=Path('/home/mj-kang/Documents/Dev/math/openai-proof-research/frontier/campaigns/2026-10-27/new-discoveries-batch2/new-twenty-2026-10-31/splitmatch-review-r1')
for name in ['openalex-citing-published','openalex-title']:
 a=json.loads((L/'downloads'/name/'raw').read_text());print(name,a['meta']);
 for r in a['results']:print(r['id'],r['title'],r['publication_date'],r.get('cited_by_count'),r.get('primary_location'))
a=json.loads((L/'downloads/pool-tree/raw').read_text());assert not a.get('truncated');p=json.loads((L/'downloads/pool-head/raw').read_text())['sha']
paths=[x['path'] for x in a['tree'] if x['type']=='blob' and x['path'].startswith('candidates/')]
print('CANDIDATE PATHS',paths)
(L/'pool-plan.tsv').write_text(''.join('pool-candidate-'+str(i)+'\thttps://raw.githubusercontent.com/Vilin97/lean-pool/'+p+'/'+path+'\n' for i,path in enumerate(paths)))
