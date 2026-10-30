from pathlib import Path
import ast
P=Path(__file__).resolve().parent
(P/'verify.py').write_text((P.parent/'root-r210-handback/verify.py').read_text().replace("orig=Path(r['original'])", "orig=Path(r.get('original',r.get('reference_absolute')))"))
t=(P.parent/'root-r184-handback/integrate.py').read_text()
old=next(ast.literal_eval(n.value) for n in ast.parse(t).body if isinstance(n,ast.Assign) and any(isinstance(x,ast.Name) and x.id=='intro' for x in n.targets))
intro='r211 Krasniqi factorial separation remains unresolved. Square cases require uniform exclusion of consecutive coprime factorial-divisor partitions; residual odd-prime exponents also remain. Fixed finite congruences cannot eliminate n!+1. Root exact replay and scientific/manifest/reference checks pass; claimed public Brocard proof defect retained without worldwide priority clearance. See root-r211-handback; fresh arithmetic r214 assigned. Counts 9 additional / 39 total, next 40.\n\n'
t=t.replace('sol-fresh-source-discovery-r184','sol-fresh-source-discovery-r211').replace(repr(old),repr(intro)).replace('Preserve uniform quadrature and rearrangement proof gaps','Preserve factorial separation and residual exponent gaps')
(P/'integrate.py').write_text(t)
