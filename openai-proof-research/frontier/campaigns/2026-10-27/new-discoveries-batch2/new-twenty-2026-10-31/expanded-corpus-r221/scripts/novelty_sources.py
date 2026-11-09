import pathlib,json,sys
sys.path.insert(0,str(pathlib.Path(__file__).resolve().parent));from fetch import get
D=pathlib.Path(__file__).resolve().parents[1]
sha=json.loads((D/'sources/pool-head.json').read_text())['sha']
get('pool-saxl-main.lean','https://raw.githubusercontent.com/Vilin97/lean-pool/'+sha+'/LeanPool/CommonNeighbourConjecture/Examples/MainTheorems.lean')
get('rowmotion-old-abs.html','https://arxiv.org/abs/2307.08520')
get('rowmotion-old.html','https://arxiv.org/html/2307.08520v2')
get('rowmotion-github-search.json','https://api.github.com/search/repositories?q=rowmotion+homomesy+lean')
