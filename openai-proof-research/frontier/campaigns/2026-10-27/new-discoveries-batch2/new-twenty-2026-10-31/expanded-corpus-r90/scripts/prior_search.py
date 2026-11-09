from fetch import get,D
from urllib.parse import urlencode
import concurrent.futures,json
qs={354090:'triangular partitions Schur',355087:'Grothendieck Gao positivity',356913:'tangent conics Newton quadrilateral',357903:'hook length biases odd distinct',359682:'descendent matroid',364498:'residue class biases partitions',366902:'fractional isometric path grids',366910:'spectral projectors surfaces revolution',367213:'clique covering Johnson lexicode',371812:'logarithmic jet conics',371841:'generalized overcubic partitions',372139:'potent 5-potent finite fields',372205:'XOR magic graphs',372390:'codegree Turan rational density',372462:'off diagonal Ramsey super exponential',372471:'multipath bidirectional polygonal',372491:'uniform sets sumsets',373644:'permutation avoidance game',404578:'hypergraph orientation head disjoint',405049:'induced subdivisions sparse graphs'}
todo=[(f'search-{i}.html','https://arxiv.org/search/?'+urlencode({'query':q,'searchtype':'all','abstracts':'show','order':'-announced_date_first','size':50})) for i,q in qs.items()]
(D/'outputs/search-queries.json').write_text(json.dumps(qs,indent=2)+'\n')
with concurrent.futures.ThreadPoolExecutor(max_workers=2) as ex:
 for r in ex.map(get,todo):print(r,flush=True)
