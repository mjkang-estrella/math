import json,pathlib,re
D=pathlib.Path(__file__).resolve().parents[1]
pat=re.compile('rayleigh|matroid|gaussoid|splitter|singularsplit|switching|schubert|lindel|koyama|ktv|swapchain|monomialdigraph|laplacianspread|foldedhyper|spectraldata|robin|grafting|poonen|intersectionclosed|unionclosed|semicomplete|eulerian|ppconstruct|cvector|associahed|booleandim|minimalbrick',re.I)
r={}
for name in ['pool','math','omega']:
 head=json.loads((D/f'sources/{name}-head.body').read_text());tree=json.loads((D/f'sources/{name}-tree.body').read_text())
 matches=[x for x in tree.get('tree',[]) if pat.search(x['path'])]
 r[name]={'head':head.get('sha'),'tree_sha':tree.get('sha'),'truncated':tree.get('truncated'),'matches':matches}
 print(name,r[name]['head'],'truncated',r[name]['truncated'])
 for x in matches:print(x['path'])
(D/'registry-screen.json').write_text(json.dumps(r,indent=2)+'\n')
