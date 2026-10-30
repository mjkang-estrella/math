from pathlib import Path
P=Path(__file__).resolve().parent
s=(P.parent/'root-r174-handback/integrate.py').read_text().replace('r174','r177')
start=s.index('intro=');end=s.index('\nn=',start)
s=s[:start]+"intro='r177 irregularising-walk Conjecture7.1 unresolved: joint Euler support/parity, budget and neighbor-separation existence missing. Root replay of 770 graphs and18247 restricted trees byte-identical; full freeze passes. Source/companion gaps preserved; no partial-family credit. See root-r177-handback. Fresh structural r180 assigned; r178/r179 continue. Counts9additional/39total,next40.\\n\\n'"+s[end:]
s=s.replace('Preserve permutation-game gap and hypermatrix public exclusion','Preserve irregularising-walk universal gap and exact controls')
(P/'integrate.py').write_text(s)
