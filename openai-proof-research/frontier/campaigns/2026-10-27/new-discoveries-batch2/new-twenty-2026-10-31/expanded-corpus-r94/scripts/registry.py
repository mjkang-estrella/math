from fetch import get,D
import json
for name,repo in [('omega','the-omega-institute/trureturing'),('openai','openai/math')]:
 o=json.loads((D/f'sources/{name}-head.json').read_text());print(get((name+'-tree.json',o['commit']['tree']['url'])))
 t=json.loads((D/f'sources/{name}-tree.json').read_text())
 wanted=['D5','Problems'] if name=='omega' else ['preprints']
 for e in t['tree']:
  if e['path'] in wanted:print(get((name+'-'+e['path']+'.json',e['url']+'?recursive=1')))
