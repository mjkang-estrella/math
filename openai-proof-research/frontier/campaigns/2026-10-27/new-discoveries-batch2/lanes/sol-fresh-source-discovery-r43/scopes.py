exec((__import__('pathlib').Path(__file__).parent/'registry.py').read_text().split('for k,r,b')[0])
for k,r in [('openai','openai/math'),('aim','MColbrook/AIM'),('count','suvrit/count-ex-machina'),('omega-main','the-omega-institute/trureturing')]:
 h=json.loads((P/'sources'/f'{k}-head.json').read_text())['sha']
 if k=='openai':
  root=fetch(k+'-root.json',f'https://api.github.com/repos/{r}/git/trees/{h}')
  sha=next(x['sha'] for x in root['tree'] if x['path']=='preprints')
  d=fetch(k+'-preprints.json',f'https://api.github.com/repos/{r}/git/trees/{sha}?recursive=1')
 else:d=fetch(k+'-tree.json',f'https://api.github.com/repos/{r}/git/trees/{h}?recursive=1')
 assert not d.get('truncated'),k
 print('COMPLETE',k,len(d['tree']))
 for x in d['tree']:
  if any(t in x['path'].lower() for t in ['sombor','movahedi','diminished']):print('MATCH',k,x['path'])
