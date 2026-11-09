from pathlib import Path
D=Path(__file__).resolve().parents[1];s=(D/'scripts/fractional.py').read_text().replace('for n in [2,3,4]:','for n in [4]:').replace('if n==4 and any(set(e)<set(g) for e in es for g in es):continue','').replace('for q in [1,2,3,4]:','for q in [1,2,3,4]:').replace("'nonempty inclusion antichains (not all hypergraphs)'","'all nonempty hypergraphs'").replace("outputs/fractional.json","outputs/fractional-deeper.json")
(D/'scripts/fractional-deeper.py').write_text(s)
