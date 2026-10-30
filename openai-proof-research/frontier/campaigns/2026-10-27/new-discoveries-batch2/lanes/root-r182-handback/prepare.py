from pathlib import Path
P=Path(__file__).resolve().parent;T=P.parent/'root-r174-handback'
s=(T/'verify.py').read_text().replace('r174','r182')
s=s.replace("-{'finalmanifest.json','manifest-verification.json'}==set(names)","-set(j['exclusions'])==set(names)")
s=s.replace("shutil.copyfile(S/'checks.py',P/'checks.py')","for r in json.loads((S/'original-copy-provenance.json').read_text()):\n a=S.parents[5]/r['original'];b=S/r['copy'];assert a.read_bytes()==b.read_bytes() and sha(b)==r['sha256']\ng=json.loads((S/'guard-binding.json').read_text());assert sha(Path(g['path']))==g['sha256']\nshutil.copyfile(S/'checks.py',P/'checks.py')")
s=s.replace('Selected shadow stabilization controls only; no all-k separation proof. Full k6 scan not repeated. Public proof exclusion retained without auditing its Lean certificate.','Exact finite-field identities and collisions for e=3..7 only; universal odd-degree collision theorem and effective curve bounds remain missing.')
(P/'verify.py').write_text(s)
s=(T/'integrate.py').read_text().replace('r174','r182');start=s.index('intro=');end=s.index('\nn=',start)
s=s[:start]+"intro='r182 Fernando–Kousik Q6.2 retained unresolved: Frobenius normal form and linearized derivative reduce full classification but all-odd-degree collision existence/curve threshold remain missing. Source convolution Conj5.23 excluded by complete classical bridge. Root private replay, original copies and freeze pass; see root-r182-handback. Fresh arithmetic/algebraic r185 assigned; r183/r184 continue. Counts9additional/39total,next40.\\n\\n'"+s[end:]
s=s.replace('Preserve permutation-game gap and hypermatrix public exclusion','Preserve finite-field classification reduction and universal gap')
(P/'integrate.py').write_text(s)
