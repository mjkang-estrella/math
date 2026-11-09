import pathlib,json,importlib.util
D=pathlib.Path(__file__).resolve().parents[1];spec=importlib.util.spec_from_file_location('lh',D/'scripts/http.py');h=importlib.util.module_from_spec(spec);spec.loader.exec_module(h)
terms=['courant','robin','expansion','pagenumber','coset','factorization','braiding','covariance','shareshian','rainbow','powerdomination','power_domination','unicycl','doublecover','double_cover','snark','domes','gaingraphic','gain_graphic','coprime','schroeder','latin','third','schmidt','analyticrank','analytic_rank','stern','quidd','einstein']
out={}
for repo in ['openai/math','Vilin97/lean-pool','the-omega-institute/trureturing']:
 k=repo.replace('/','-');p=D/'sources'/(k+'-tree.json')
 if not p.exists():continue
 t=json.loads(p.read_text());out[repo]={'head':json.loads((D/'sources'/(k+'-head.json')).read_text()).get('sha'),'truncated':t.get('truncated'),'hits':[x['path'] for x in t.get('tree',[]) if any(z in x['path'].lower() for z in terms)]}
 print(repo,json.dumps(out[repo],indent=2)[:10000])
 if repo=='Vilin97/lean-pool':
  for x in t.get('tree',[]):
   if x['type']=='blob' and (x['path']=='projects.yml' or x['path'].startswith('candidates/')):h.get('lean-pool-'+x['path'].replace('/','__'),'https://raw.githubusercontent.com/'+repo+'/'+out[repo]['head']+'/'+x['path'])
for p in (D/'sources').glob('lean-pool-*'):
 if '.json' in p.name:continue
 lines=[l for l in p.read_text(errors='replace').splitlines() if any(z in l.lower() for z in terms)];out[p.name]=lines;print(p.name,'\n'.join(lines)[:8000])
(D/'registry-screen.json').write_text(json.dumps(out,indent=2)+'\n')
