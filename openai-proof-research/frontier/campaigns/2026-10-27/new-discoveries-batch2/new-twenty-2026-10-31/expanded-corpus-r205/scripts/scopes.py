import sys,pathlib,json,runpy,re
D=pathlib.Path(sys.argv[1]).resolve();sys.argv=sys.argv[:2];fetch=runpy.run_path(str(D/'scripts/fetch.py'))['fetch']
for repo in ['Vilin97-lean-pool','openai-math','the-omega-institute-trureturing']:
 t=json.loads((D/f'sources/{repo}-tree/body').read_text());h=json.loads((D/f'sources/{repo}-head/body').read_text())['sha'];name={'Vilin97-lean-pool':'Vilin97/lean-pool','openai-math':'openai/math','the-omega-institute-trureturing':'the-omega-institute/trureturing'}[repo]
 for x in t['tree']:
  p=x['path']
  if repo=='Vilin97-lean-pool' and p.endswith('projects.yml'):fetch('https://raw.githubusercontent.com/'+name+'/'+h+'/'+p,'pool-projects-found')
  if (repo=='the-omega-institute-trureturing' and p in ['D5','Problems']) or (repo=='openai-math' and p=='preprints'):
   fetch('https://api.github.com/repos/'+name+'/git/trees/'+x['sha']+'?recursive=1','scope-'+repo+'-'+p)
for label,url in [('dilates-correct','https://arxiv.org/pdf/2508.18586'),('factors-vor','https://people.math.ethz.ch/~sudakovb/factors-hamiltonian-graphs.pdf'),('bean-old','https://www.numdam.org/item/CM_1994__92_2_115_0.pdf')]:fetch(url,label)
