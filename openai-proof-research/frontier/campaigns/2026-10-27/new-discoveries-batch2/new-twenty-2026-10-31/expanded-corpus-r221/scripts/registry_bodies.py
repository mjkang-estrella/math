import pathlib,json,sys
sys.path.insert(0,str(pathlib.Path(__file__).resolve().parent));from fetch import get
D=pathlib.Path(__file__).resolve().parents[1]
sha=json.loads((D/'sources/pool-head.json').read_text())['sha']
for p in ['LeanPool/CommonNeighbourConjecture.lean','LeanPool/CommonNeighbourConjecture/MainTheorems.lean','LeanPool/CommonNeighbourConjecture/Saxl/Generalized.lean']:
 get('pool-body-'+p.replace('/','_'),'https://raw.githubusercontent.com/Vilin97/lean-pool/'+sha+'/'+p)
sha=json.loads((D/'sources/omega-head.json').read_text())['sha']
for p in ['D5/S3/Combinatorics/Geometry/RectangleRowmotionHomomesy.lean','D5/S3/Combinatorics/Geometry/RowmotionExceptionalGeometry.lean']:
 get('omega-body-'+p.rsplit('/',1)[-1],'https://raw.githubusercontent.com/the-omega-institute/trureturing/'+sha+'/'+p)
# Nonrecursive roots recover paths omitted by truncated global trees.
for repo,key in [('the-omega-institute/trureturing','omega'),('openai/math','openai')]:
 sha=json.loads((D/f'sources/{key}-head.json').read_text())['sha'];r=get(key+'-root.json',f'https://api.github.com/repos/{repo}/git/trees/{sha}')
 if r.get('status')==200:
  for x in json.loads((D/f'sources/{key}-root.json').read_text()).get('tree',[]):
   if x['path'] in ['Problems','preprints']:get(key+'-'+x['path']+'-fulltree.json',f'https://api.github.com/repos/{repo}/git/trees/'+x['sha']+'?recursive=1')
