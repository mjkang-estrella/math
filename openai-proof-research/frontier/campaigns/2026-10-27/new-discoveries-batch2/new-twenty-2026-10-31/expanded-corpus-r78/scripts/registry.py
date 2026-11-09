from fetch import *
h=json.loads((D/'sources/omega-head.json').read_text());sha=h['sha'];get(('omega-tree.json',f'https://api.github.com/repos/the-omega-institute/trureturing/git/trees/{sha}'))
r=json.loads((D/'sources/omega-tree.json').read_text())
for o in r.get('tree',[]):
 if o['path'] in ['D5','Problems']:get(('omega-'+o['path']+'.json',f"https://api.github.com/repos/the-omega-institute/trureturing/git/trees/{o['sha']}?recursive=1"))
print([(o['path'],o['type']) for o in r.get('tree',[])])
