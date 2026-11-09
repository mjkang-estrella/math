from pathlib import Path
s=(Path(__file__).parent/'search_history.py').read_text()
s=s.replace("pattern=r'Shareshian|chromatic.quasisymmetric|elementary.unimod|e.unimodal|theta.section|Lefschetz.*(graph|chromatic)|T169|I169|Foulkes'", "pattern=r'projected.{0,60}(common|base)|common.{0,60}project|matroid.union|hidden.{0,40}contraction|distinct.{0,30}projected'")
s=s.replace('search/history-search.json','search/projection-search.json')
s=s[:s.index('for p in hits:')]+"print('Original authored hit list retained privately; next reads targeted.')\n"
exec(compile(s,__file__,'exec'))
