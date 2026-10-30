from pathlib import Path
P=Path(__file__).resolve().parent
s=(P.parent/'root-r180-handback/integrate.py').read_text().replace('r180','r184');start=s.index('intro=');end=s.index('\nn=',start)
s=s[:start]+"intro='r184 Gauss–Legendre uniform circle and Cheeger–Kohler–Jobin questions remain unresolved. Sonin correction and rearrangement support/rigidity gaps explicit; hypothetical envelope control is not source counterexample. Root symbolic replay and local/external freeze pass; see root-r184-handback. Fresh analytic r187 assigned; r185/r186 continue. Counts9additional/39total,next40.\\n\\n'"+s[end:]
s=s.replace('Record Cayley public refutation and prior target exclusions','Preserve uniform quadrature and rearrangement proof gaps')
(P/'integrate.py').write_text(s)
