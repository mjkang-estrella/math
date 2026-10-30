from pathlib import Path
P=Path(__file__).resolve().parent
s=(P.parent/'root-r180-handback/integrate.py').read_text().replace('r180','r181');start=s.index('intro=');end=s.index('\nn=',start)
s=s[:start]+"intro='r181 zero nominations: Poisson mean-constant and two Wasserstein/Poincare assertions retired by actual public bodies, with original-question attribution limit preserved. Root exact positive-test replay matches all mathematical fields; local/external science and manifest pass. See root-r181-handback. Fresh analytic r184 assigned; r182/r183 continue. Counts9additional/39total,next40.\\n\\n'"+s[end:]
s=s.replace('Record Cayley public refutation and prior target exclusions','Record Poisson and Wasserstein public-result exclusions')
(P/'integrate.py').write_text(s)
