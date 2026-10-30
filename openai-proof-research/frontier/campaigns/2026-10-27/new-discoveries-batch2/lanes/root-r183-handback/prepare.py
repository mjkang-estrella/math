from pathlib import Path
P=Path(__file__).resolve().parent;T=P.parent/'root-r174-handback'
s=(T/'verify.py').read_text().replace('r174','r183')
s=s.replace('Selected shadow stabilization controls only; no all-k separation proof. Full k6 scan not repeated. Public proof exclusion retained without auditing its Lean certificate.','Restricted clique-star formula, finite optimization and split controls only; no universal connected-graph bound or equality classification.')
(P/'verify.py').write_text(s)
s=(T/'integrate.py').read_text().replace('r174','r183');start=s.index('intro=');end=s.index('\nn=',start)
s=s[:start]+"intro='r183 induced-matching Conjecture4.1 remains unresolved: clique-star count/splitting helpers lack universal connected extremal reduction, all-n optimization and equality classification. Root exact replay and full freeze pass; repaired checker failures and source holds retained. See root-r183-handback. Fresh structural r186 assigned; r184/r185 continue. Counts9additional/39total,next40.\\n\\n'"+s[end:]
s=s.replace('Preserve permutation-game gap and hypermatrix public exclusion','Preserve induced-matching extremal reduction gaps')
(P/'integrate.py').write_text(s)
