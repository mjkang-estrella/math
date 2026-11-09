import json
from fetch import get,D
h=json.loads((D/'sources/omega-head.json').read_text())
print(get(('omega-root-tree.json',h['commit']['tree']['url']+'?recursive=1')))
