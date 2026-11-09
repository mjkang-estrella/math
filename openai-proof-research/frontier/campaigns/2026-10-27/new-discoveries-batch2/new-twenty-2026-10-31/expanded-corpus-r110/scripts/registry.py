from fetch import get,D
import json,re
heads={k:json.loads((D/'sources'/f'{k}-head.json').read_text())['sha'] for k in ['omega','openai']}
repos={'omega':'the-omega-institute/trureturing','openai':'openai/math'}
for k in heads:
 get((f'{k}-root.json',f'https://api.github.com/repos/{repos[k]}/git/trees/{heads[k]}'))
 root=json.loads((D/'sources'/f'{k}-root.json').read_text())
 for e in root.get('tree',[]):
  if e['path'] in (['D5','Problems'] if k=='omega' else ['preprints']):
   get((f'{k}-{e["path"]}.json',e['url']+'?recursive=1'))
paths={}
for p in (D/'sources').glob('*.json'):
 if p.stem in ['omega-D5','omega-Problems','openai-preprints']:
  a=json.loads(p.read_text());paths[p.name]={'truncated':a.get('truncated'),'matches':[e for e in a.get('tree',[]) if re.search(r'339514|340195|340354|340430|340474|375504|374063|374244|375364|366897|371616|364032|357510|358215|359747|353371|347533|348488|348697|342772|cactus|loopy|Petersen.*flow|prefix.*revers|unicyclic|Shannon|MaySpectral|CyclicRamsey|AffineMeasurement|tropical.*chrom|balanced.*cyclic',e['path'],re.I)]}
(D/'outputs/registry-screen.json').write_text(json.dumps({'heads':heads,'path_screen_only':paths},indent=2))
print(json.dumps(paths,indent=2))
