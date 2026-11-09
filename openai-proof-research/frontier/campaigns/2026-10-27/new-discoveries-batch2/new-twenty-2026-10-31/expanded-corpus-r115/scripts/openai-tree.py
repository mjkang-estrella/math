from fetch import D,get
import json
h=json.loads((D/'sources/openai-head.json').read_text())['sha'];get(('openai-root.json',f'https://api.github.com/repos/openai/math/git/trees/{h}'))
o=json.loads((D/'sources/openai-root.json').read_text())
for t in o['tree']:
 if t['path']=='preprints':print(get(('openai-preprints.json',f'https://api.github.com/repos/openai/math/git/trees/{t["sha"]}?recursive=1')))
