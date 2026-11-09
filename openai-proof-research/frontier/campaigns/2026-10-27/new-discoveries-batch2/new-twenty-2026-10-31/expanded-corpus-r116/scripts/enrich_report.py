import json
from pathlib import Path
D=Path(__file__).resolve().parents[1];r=json.loads((D/'results.json').read_text())
for i,name in [('363664','pal-bwt-300'),('362627','thin-5-3-10')]:
 r[i]['last_structured_search_output']=json.loads((D/'outputs'/f'{name}.json').read_text())
for i in ['363397','363398']:r[i]['logs']=list(dict.fromkeys(r[i]['logs']+['logs/words-clean.log']))
games=[]
for f in sorted((D/'outputs').glob('game-*.json')):games.append(json.loads(f.read_text()))
r['364033']['exact_game_outputs']=games
r['364033']['logs']=[str(f.relative_to(D)) for f in sorted((D/'logs').glob('game*.log'))]
r['364033']['mathematical_attempts_and_coverage']+=' Exact score DP outputs and complete-state counts are in exact_game_outputs; no finite match proves the general score bridge.'
(D/'results.json').write_text(json.dumps(r,indent=2,ensure_ascii=False)+'\n')

r['362628']['review_depth'] += ' Appendix proofs C.6 and C.7 read: localization denominator clearing proves both inclusions.'
r['364350']['review_depth'] += ' Full Theorem4.4 proof read: Morse critical-cell correction, link/deletion wedges and binomial recursion.'
(D/'results.json').write_text(json.dumps(r,indent=2,ensure_ascii=False)+'\n')
