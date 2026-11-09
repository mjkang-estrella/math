import sys,json,pathlib
sys.path.insert(0,str(pathlib.Path(__file__).resolve().parent));from fetch_http import get
D=pathlib.Path(__file__).resolve().parents[1]
for repo,key in [('Vilin97/lean-pool','leanpool'),('openai/math','openai'),('the-omega-institute/trureturing','omega')]:get(key+'-head.json','https://api.github.com/repos/'+repo+'/commits/HEAD')
for aid in sorted({o['source_url'].split('/')[-1] for o in json.loads((D/'extracted.json').read_text()).values()}):get(aid+'-abs.html','https://arxiv.org/abs/'+aid)
