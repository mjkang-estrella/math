from fetch import get,D
import json
for name,repo in [('omega','the-omega-institute/trureturing'),('openai','openai/math')]:
 h=json.loads((D/f'sources/{name}-head.json').read_text());print(name,h['sha'])
 get((name+'-root.json',f"https://api.github.com/repos/{repo}/git/trees/{h['commit']['tree']['sha']}"))
 root=json.loads((D/f'sources/{name}-root.json').read_text())
 if name=='openai':
  targets=[x for x in root['tree'] if x['path']=='preprints']
 else:
  targets=[x for x in root['tree'] if x['path'] in ['Problems','D5']]
 for x in targets:get((name+'-'+x['path']+'-tree.json',x['url']+'?recursive=1'))
 print('targets',[(x['path'],x['sha']) for x in targets])
