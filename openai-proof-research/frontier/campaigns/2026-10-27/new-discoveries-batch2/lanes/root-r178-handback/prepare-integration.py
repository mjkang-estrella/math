from pathlib import Path
P=Path(__file__).resolve().parent
s=(P.parent/'root-r174-handback/integrate.py').read_text().replace('r174','r178')
start=s.index('intro=');end=s.index('\nn=',start)
s=s[:start]+"intro='r178 zero nominees: Gaussian split target duplicates r47; Karp–Sitnik Kummer ratio and Nikolov snake positivity have exact public resolutions. Root actual-scope review, exact certificate replay and full freeze pass; see root-r178-handback. Fresh analytic r181 assigned; r179/r180 continue. Counts9additional/39total,next40.\\n\\n'"+s[end:]
s=s.replace('Preserve permutation-game gap and hypermatrix public exclusion','Record exact Kummer and snake public-result exclusions')
(P/'integrate.py').write_text(s)
