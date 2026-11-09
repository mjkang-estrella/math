import pathlib,sys,runpy,json,re
D=pathlib.Path(sys.argv[1]).resolve();sys.argv=sys.argv[:2];fetch=runpy.run_path(str(D/'scripts/fetch.py'))['fetch']
for label,url in [('kwan-vor','https://people.math.ethz.ch/~sudakovb/multi-part-hilton-milner.pdf'),('katona-follow','https://real.mtak.hu/115975/1/P01.pdf'),('galashin-vor','https://www.math.ucla.edu/~galashin/papers/separation.pdf'),('group-original','https://research-repository.st-andrews.ac.uk/bitstream/handle/10023/10576/Cameron_2017_Generating_TAMS_AAM.pdf?sequence=1')]:fetch(url,label)
# Scope roots are inspected by explicit SHA even where root recursive tree truncates.
for repo,label in [('the-omega-institute/trureturing','omega'),('openai/math','openai')]:
 h=json.loads((D/('sources/'+('the-omega-institute-trureturing' if label=='omega' else 'openai-math')+'-head/body')).read_text())['sha']
 x=fetch('https://api.github.com/repos/'+repo+'/git/trees/'+h,'root-'+label)
 if x:
  for z in x['tree']:
   if z['path'] in ['Problems','preprints']:fetch('https://api.github.com/repos/'+repo+'/git/trees/'+z['sha']+'?recursive=1','full-'+label+'-'+z['path'])
