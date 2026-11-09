import pathlib,json,runpy,re
D=pathlib.Path(__file__).resolve().parents[1];f=runpy.run_path(str(D/'scripts/fetch.py'))['fetch']
for repo,label,names in [('openai/math','openai-math',['preprints']),('the-omega-institute/trureturing','the-omega-institute-trureturing',['D5','Library','Blueprint'])]:
 sha=json.loads(next(D.glob('http/*'+label+'-head-0.body')).read_text())[0]['sha'];r=f('https://api.github.com/repos/'+repo+'/git/trees/'+sha,label+'-root')
 for t in json.loads((D/r['steps'][-1]['file']).read_text()).get('tree',[]):
  if t['path'] in names:f('https://api.github.com/repos/'+repo+'/git/trees/'+t['sha']+'?recursive=1',label+'-'+t['path'])
f('https://arxiv.org/pdf/2607.18746','schubert-prior')
f('https://arxiv.org/abs/2607.18746','schubert-prior-abs')
