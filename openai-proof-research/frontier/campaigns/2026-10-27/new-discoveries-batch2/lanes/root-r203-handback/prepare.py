from pathlib import Path
import ast
P=Path(__file__).resolve().parent
v=(P.parent/'root-r201-handback/verify.py').read_text().replace('sol-fresh-source-discovery-r201','sol-fresh-source-discovery-r203')
v=v.replace("set(m['explicit_exclusions'])=={r['path'] for r in m['files']}","set(m['excludes'])==set(m['files'])")
v=v.replace("for r in m['files']:assert sha(S/r['path'])==r['sha256'] and (S/r['path']).stat().st_size==r['bytes']","for n,h in m['files'].items():assert sha(S/n)==h")
v=v.replace("originals()\ndrift=","aliases=json.loads((S/'legacy-alias-refresh.json').read_text())['records']\nfor r in aliases:assert sha(S/r['copy'])==r['sha256']\ng=json.loads((S/'guard-binding.json').read_text());assert sha(Path(g['original']))==sha(S/g['copy'])==g['sha256']\noriginals()\ndrift=")
v=v.replace('Pointwise algebra controls only; no universal rigidity theorem.','Exact radix and support controls only; no universal additive-complement gap theorem.')
(P/'verify.py').write_text(v)
t=(P.parent/'root-r184-handback/integrate.py').read_text()
old=next(ast.literal_eval(n.value) for n in ast.parse(t).body if isinstance(n,ast.Assign) and any(isinstance(x,ast.Name) and x.id=='intro' for x in n.targets))
intro='r203 almost-perfect additive-complement gap Conjecture1.3 remains unresolved. Perfect-subclass radix gap and global3/2 lower bound are known; subsequential factorization gives no all-scale upper bound. Root exact replay and primary/manifest/reference integrity pass. Finch Conjecture14 also unresolved, small-index correction uncredited. See root-r203-handback; fresh arithmetic r205 assigned. Counts 9 additional / 39 total, next 40.\n\n'
t=t.replace('sol-fresh-source-discovery-r184','sol-fresh-source-discovery-r203').replace(repr(old),repr(intro)).replace('Preserve uniform quadrature and rearrangement proof gaps','Preserve additive complement gap and missing global transfer')
(P/'integrate.py').write_text(t)
