from pathlib import Path
P=Path(__file__).resolve().parent
s=(P.parent/'root-r174-handback/integrate.py').read_text().replace("S=P.parent/'sol-fresh-source-discovery-r174'","S=P.parent/'sol-dsbs-published-source-prior-review-r2'")
start=s.index('intro=');end=s.index('\nn=',start)
s=s[:start]+"intro='DSBS source review r2: retain ordinary mathematics PASS and qualified positive substantive assessment, but investment HOLD. Three journal-body comparisons remain open; author listings and arXiv bodies do not authenticate VoR changes. Park repeated access searches absent a concrete new route. Root read-only verifier and full manifest/freeze pass; see root-dsbs-source-hold-r2. Fresh structural r177 assigned; r175/r176 continue. Counts 9 additional /39 total, next40.\\n\\n'"+s[end:]
s=s.replace('Preserve permutation-game gap and hypermatrix public exclusion','Preserve DSBS journal-body holds and bounded positive review')
(P/'integrate.py').write_text(s)
