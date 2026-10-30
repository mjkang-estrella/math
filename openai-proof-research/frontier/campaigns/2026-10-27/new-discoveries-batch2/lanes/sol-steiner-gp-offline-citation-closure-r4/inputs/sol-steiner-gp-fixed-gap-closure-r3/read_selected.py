from work import *
ds=json.loads((L/'semantic-selection.json').read_text())
for x in ds:
 p=x['new_path']
 if p.endswith('.md') and ('/Graph/' in p or 'Nonconvex' in p):
  s=(L/x['body']).read_text();print('\nBODY',p,'removed',x['removed'],'added',x['added'],'\n',s[:6500])
print('all relevant hits')
for x in ds:
 if x['hits']:print(x['new_path'],x['hits'][:3])
print('counts',[(x['commit'],len(x['files'])) for x in json.loads((L/'diff-coverage.json').read_text())])
