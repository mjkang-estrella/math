from pathlib import Path
P=Path(__file__).resolve().parent;T=P.parent/'root-r174-handback'
s=(T/'verify.py').read_text().replace('r174','r176')
s=s.replace("{'finalmanifest.json','manifest-verification.json'}","{'finalmanifest.json','manifest-verification.json','verification-guard.json'}")
s=s.replace("shutil.copyfile(S/'checks.py',P/'checks.py')","for r in json.loads((S/'scientific-freeze.json').read_text())['administrative_snapshots']:check(S/r['path'],r)\nshutil.copyfile(S/'checks.py',P/'checks.py')")
s=s.replace('Selected shadow stabilization controls only; no all-k separation proof. Full k6 scan not repeated. Public proof exclusion retained without auditing its Lean certificate.','Exact finite Hilbert/rook diagnostics only; no universal counting identity or regularity bridge. Initial extra-log verification failure preserved.')
(P/'verify.py').write_text(s)
s=(T/'integrate.py').read_text().replace('r174','r176')
start=s.index('intro=');end=s.index('\nn=',start)
s=s[:start]+"intro='r176 switching-rook Conjecture2.4 remains unresolved: all-degree monomial-congruence reduction lacks uniform counting identity and separate regularity bridge. Karapetyan even-degree correction excluded as source adaptation. Root private exact replay and full freeze verify; initial extra-log verification failure preserved. See root-r176-handback. Fresh arithmetic/algebraic r179 assigned; r177/r178 continue. Counts9additional/39total,next40.\\n\\n'"+s[end:]
s=s.replace('Preserve permutation-game gap and hypermatrix public exclusion','Preserve switching-rook counting and regularity gaps')
(P/'integrate.py').write_text(s)
