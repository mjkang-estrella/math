import sys,pathlib,json,re
exec((pathlib.Path(__file__).parent/'fetch.py').read_text())
if mode=='more':
 sha=json.loads((D/'sources/lean-pool-head.json').read_text())['sha']
 for p in ['LeanPool/CommonNeighbourConjecture/Examples/MainTheorems.lean','LeanPool/CommonNeighbourConjecture/Saxl/Basic.lean']:
  get(f'https://raw.githubusercontent.com/Vilin97/lean-pool/{sha}/{p}','pool-'+p.replace('/','_'))
 for a in ['2411.19587','2410.22245','2301.13563','2412.15457','2412.18938']:
  s=(D/'sources'/f'{a}-abs.html').read_text();vs=sorted(set(re.findall(r'\[v(\d+)\]',s)))
  print(a,vs,flush=True)
  for v in vs:get('https://arxiv.org/html/'+a+'v'+v,a+'v'+v+'-body.html')
