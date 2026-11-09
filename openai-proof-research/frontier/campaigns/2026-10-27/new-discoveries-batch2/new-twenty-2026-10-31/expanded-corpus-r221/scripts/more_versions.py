import pathlib,json,sys,re
sys.path.insert(0,str(pathlib.Path(__file__).resolve().parent));from fetch import get
D=pathlib.Path(__file__).resolve().parents[1]
# Every version of routes actually pursued; other routes remain explicitly version-limited.
for a,vs in [('2503.18554',[1,2,3,4]),('2504.00834',[1,2]),('2504.00768',[1,2]),('2505.00874',[1,2,3])]:
 for v in vs:get(a+f'v{v}.html',f'https://arxiv.org/html/{a}v{v}')
get('omega-signed-history.json','https://api.github.com/repos/the-omega-institute/trureturing/commits?path=D5/S3/Combinatorics/Geometry/IntervalClosedSignedCardinalityRefutation.lean&per_page=10')
get('saxl-repo-head.json','https://api.github.com/repos/alunik/common-neighbour-conjecture/commits/HEAD')
