import pathlib,json,sys,re
sys.path.insert(0,str(pathlib.Path(__file__).resolve().parent));from fetch import get
D=pathlib.Path(__file__).resolve().parents[1]
sha=json.loads((D/'sources/omega-head.json').read_text())['sha']
get('omega-signed-refutation.lean',f'https://raw.githubusercontent.com/the-omega-institute/trureturing/{sha}/D5/S3/Combinatorics/Geometry/IntervalClosedSignedCardinalityRefutation.lean')
get('omega-signed-dossier.md',f'https://raw.githubusercontent.com/the-omega-institute/trureturing/{sha}/Problems/elder-lafreniere-conjecture-4-12-signed-cardinality-refutation.md')
get('fox-tidor-paper.html','https://drops.dagstuhl.de/entities/document/10.4230/LIPIcs.SoCG.2026.50')
pat=re.compile(r'intervalclosed|signedcardinal|colbourn|subsquare|perfectdivis|kleinbottle|suspension.*tree|glued.*poset|gluing.*poset|anastos|fabian|szabo|three.*matching|matching.*multipli|chromatic.*homol|blaschke|self.*guard|ising.*map|sphere.*intersect|rigidity.*polytop',re.I)
for name in ['omega-D5-tree.json','omega-Problems-fulltree.json','openai-preprints-fulltree.json']:
 t=json.loads((D/'sources'/name).read_text());print(name,'truncated',t.get('truncated'))
 for x in t['tree']:
  if pat.search(x['path']):print(x['path'])
