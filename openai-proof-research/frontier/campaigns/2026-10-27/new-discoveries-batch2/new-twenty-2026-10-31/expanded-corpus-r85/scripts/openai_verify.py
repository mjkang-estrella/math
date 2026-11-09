from fetch import get,D
import json
print(get(('openai-root.json','https://api.github.com/repos/openai/math/git/trees/4eaee87548250b2682affda7d05d947c05554bae')))
o=json.loads((D/'sources/openai-root.json').read_text())
print([x for x in o['tree'] if x['path']=='preprints'])
