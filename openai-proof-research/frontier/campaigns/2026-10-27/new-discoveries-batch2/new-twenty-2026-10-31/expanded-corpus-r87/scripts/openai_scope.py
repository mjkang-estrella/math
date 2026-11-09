from fetch import D,get
import json,hashlib
h=json.loads((D/'sources/openai-head.json').read_text());print(get(('openai-root-direct.json',h['commit']['tree']['url'])))
f=D/'sources/openai-root-direct.json'
if f.exists():
 cached=D.parent/'fresh-corpus-r10/sources/registry-preprints.json';c=json.loads(cached.read_text())
 entry=next(x for x in json.loads(f.read_text())['tree'] if x['path']=='preprints')
 out=dict(live_head=h['sha'],live_preprints_tree=entry['sha'],cached_preprints_tree=c['sha'],equal=entry['sha']==c['sha'],cached_file=str(cached),cached_sha256=hashlib.sha256(cached.read_bytes()).hexdigest(),cached_truncated=c.get('truncated'),scope='Exact subtree byte hash reuse; path screen is not body review')
 (D/'outputs/openai-cache-binding.json').write_text(json.dumps(out,indent=2)+'\n');print(out)
