import sys,json,pathlib
sys.path.insert(0,str(pathlib.Path(__file__).resolve().parent));from fetch_http import get
D=pathlib.Path(__file__).resolve().parents[1]
for key,repo,paths in [('omega','the-omega-institute/trureturing',['D5','Problems']),('openai','openai/math',['preprints','lean'])]:
 x=json.loads((D/f'http/{key}-tree.json').read_text());sha=json.loads((D/f'http/{key}-head.json').read_text())['sha']
 for p in paths:
  ent=next((o for o in x['tree'] if o['path']==p),None)
  if ent:get(f'{key}-{p}-tree.json',f'https://api.github.com/repos/{repo}/git/trees/{ent["sha"]}?recursive=1')
 for p in (['D5/S3/Combinatorics/Graph/Walks/DemoStrongPeriodBoundRefutation.lean','Blueprint/D5/S3/Combinatorics/Graph/Walks/DemoStrongPeriodBoundRefutation.md'] if key=='omega' else ['CONTENTS.md','lean/ComparatorChallenges/OstmannComplete.lean','lean/ComparatorChallenges/OstmannPrimes.lean']):get(key+'-'+p.replace('/','-'),f'https://raw.githubusercontent.com/{repo}/{sha}/{p}')
