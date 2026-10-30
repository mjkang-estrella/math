from pathlib import Path
P=Path(__file__).resolve().parent
s=(P.parent/'root-r174-handback/integrate.py').read_text().replace('r174','r175')
start=s.index('intro=');end=s.index('\nn=',start)
s=s[:start]+"intro='r175: Xu fractional-power means conjecture excluded by complete source sum/product integral bridge; one-bit estimation remains unresolved despite periodic information shortcut obstruction. Root exact checks byte-identical and full scientific/manifest freeze pass; see root-r175-handback. Fresh analytic r178 assigned; r176/r177 continue. Counts 9 additional /39 total, next40.\\n\\n'"+s[end:]
s=s.replace('Preserve permutation-game gap and hypermatrix public exclusion','Record means adaptation and unresolved one-bit uniform-risk gap')
(P/'integrate.py').write_text(s)
