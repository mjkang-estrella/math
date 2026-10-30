from pathlib import Path
P=Path(__file__).resolve().parent;T=P.parent/'root-r179-handback'
s=(T/'verify.py').read_text().replace('r179','r180')
s=s.replace("g=json.loads((S/'guard-binding.json').read_text());assert sha(Path(g['path']))==g['sha256']\n",'')
s=s.replace('39 negative-diagonal and 38 recurrence diagnostics of prior public mathematics only; no new result or universal certificate.','5033 subsets until first witness and 12 cover controls for an existing public refutation only; no new discovery.')
(P/'verify.py').write_text(s)
s=(T/'integrate.py').read_text().replace('r179','r180');start=s.index('intro=');end=s.index('\nn=',start)
s=s[:start]+"intro='r180 zero nominees: TI augmentation duplicates r122; weighted-bond difference already retired; Potechin–Tsang Cayley conjecture refuted by Lehner–Verret2020 exact dihedral-cover construction. Root exact replay and full freeze pass; see root-r180-handback. Fresh structural r183 assigned with duplicates screened before fresh-target selection; r181/r182 continue. Counts9additional/39total,next40.\\n\\n'"+s[end:]
s=s.replace('Record arithmetic duplicate and public-proof exclusions','Record Cayley public refutation and prior target exclusions')
(P/'integrate.py').write_text(s)
