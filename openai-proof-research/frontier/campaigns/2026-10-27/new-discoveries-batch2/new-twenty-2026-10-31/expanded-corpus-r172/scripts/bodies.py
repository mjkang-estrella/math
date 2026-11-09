import sys,pathlib,json,re
sys.path.insert(0,str(pathlib.Path(__file__).resolve().parent))
from fetch import D,fetch
repo='the-omega-institute/trureturing';sha=json.loads((D/'sources/the-omega-institute-trureturing-head.json').read_text())['sha']
paths=['D5/S3/Combinatorics/Geometry/MiuraResolution.lean','D5/S3/ConceptDynamics/GraphColoring/GraphCoverDomination.lean']
for x in json.loads((D/'sources/the-omega-institute-trureturing-Problems.json').read_text())['tree']:
 if re.search(r'miura|domination.*cover|cover.*domination|paper.boat|luroth|regular.genus|cactus|pebbling|higher.bruhat|degree.power|bounded.matching',x['path'],re.I):paths.append('Problems/'+x['path'])
for p in paths:fetch('https://raw.githubusercontent.com/'+repo+'/'+sha+'/'+p,'omega-'+p.replace('/','-'))
