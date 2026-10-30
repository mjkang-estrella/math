from pathlib import Path
P=Path(__file__).resolve().parent
T=P.parent/'root-r173-handback'
s=(T/'verify.py').read_text().replace('r173','r174').replace('Exact relaxed-data method countermodels only; no geometric counterexample or all-triangle theorem. Numerical search not repeated.','Selected shadow stabilization controls only; no all-k separation proof. Full k6 scan not repeated. Public proof exclusion retained without auditing its Lean certificate.')
(P/'verify.py').write_text(s)
s=(T/'integrate.py').read_text().replace('r173','r174')
start=s.index("intro=");end=s.index('\nn=',start)
s=s[:start]+"intro='r174 handback: reverse permutation game all-k separation remains unproved; exact hypermatrix public proof excludes that target. Root selected-shadow replay byte-identical; payload and scientific hashes verify. See root-r174-handback. Fresh finite/algebraic r176 assigned; analytic r175 and DSBS published-source comparison continue. Counts 9 additional / 39 total, next 40.\\n\\n'"+s[end:]
s=s.replace('Preserve unresolved triangle median reductions and refill research slot','Preserve permutation-game gap and hypermatrix public exclusion')
(P/'integrate.py').write_text(s)
