from pathlib import Path
P=Path(__file__).resolve().parent;T=P.parent/'root-r174-handback'
s=(T/'verify.py').read_text().replace('r174','r179')
s=s.replace("if name=='finalmanifest.json':assert {str(p.relative_to(S)) for p in S.rglob('*') if p.is_file()}-{'finalmanifest.json','manifest-verification.json'}==set(names)","assert {str(p.relative_to(S)) for p in S.rglob('*') if p.is_file()}-set(j['exclusions'])==set(names)")
s=s.replace("shutil.copyfile(S/'checks.py',P/'checks.py')","g=json.loads((S/'guard-binding.json').read_text());assert sha(Path(g['path']))==g['sha256']\nshutil.copyfile(S/'checks.py',P/'checks.py')")
s=s.replace('Selected shadow stabilization controls only; no all-k separation proof. Full k6 scan not repeated. Public proof exclusion retained without auditing its Lean certificate.','39 negative-diagonal and 38 recurrence diagnostics of prior public mathematics only; no new result or universal certificate.')
(P/'verify.py').write_text(s)
s=(T/'integrate.py').read_text().replace('r174','r179');start=s.index('intro=');end=s.index('\nn=',start)
s=s[:start]+"intro='r179 zero nominees: Yamamura Galois target duplicates r130; Catalan irreducibility and Fayers divisibility have exact public proof bodies. Root full Fayers bridge review, private exact checks and freeze pass; see root-r179-handback. Fresh arithmetic/algebraic r182 assigned; r180/r181 continue. Counts9additional/39total,next40.\\n\\n'"+s[end:]
s=s.replace('Preserve permutation-game gap and hypermatrix public exclusion','Record arithmetic duplicate and public-proof exclusions')
(P/'integrate.py').write_text(s)
