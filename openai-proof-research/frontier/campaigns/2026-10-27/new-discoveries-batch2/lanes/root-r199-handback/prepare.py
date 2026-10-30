from pathlib import Path
import ast
P=Path(__file__).resolve().parent
v=(P.parent/'root-r198-handback/verify.py').read_text().replace('sol-fresh-source-discovery-r198','sol-fresh-source-discovery-r199').replace("(S/'checks-final.json')","(S/'checks.json')")
v=v.replace('Method diagnostics only; universal source endpoint remains unresolved. Inherited failures preserved.','Finite diagnostics only; complete ordinary candidate awaits independent scope, mathematics and substantive review. Inherited failures preserved.')
marker='originals();shutil.copyfile'
v=v.replace(marker,"""active=json.loads((S/'active-refresh.json').read_text());drift=[]
for r in active:
 assert sha(S/r['copy'])==r['sha256']
 if r['changed']:assert sha(S/r['new_copy'])==r['current_sha256']
 if sha(Path(r['original']))!=r['current_sha256']:drift.append(r['original'])
(P/'active-snapshot-check.json').write_text(json.dumps(dict(snapshot_copies='PASS',current_drift=drift,qualification='Mutable snapshots are not scientific immutable bindings'),indent=2)+'\\n')
originals();shutil.copyfile""")
(P/'verify.py').write_text(v)
t=(P.parent/'root-r184-handback/integrate.py').read_text()
old=next(ast.literal_eval(n.value) for n in ast.parse(t).body if isinstance(n,ast.Assign) and any(isinstance(x,ast.Name) and x.id=='intro' for x in n.targets))
intro='r199 normalized totient deficiency full ordinary candidate retained for independent source-scope and routine-adaptation review. Claimed mean absolute error and natural-density limits at 1; no pointwise or finite-cutoff distribution claim. Complete classical cofactor bridge supplied. Root exact replay and final integrity pass; no Lean, manuscript or credit. See root-r199-handback. Counts 9 additional / 39 total, next 40.\n\n'
t=t.replace('sol-fresh-source-discovery-r184','sol-fresh-source-discovery-r199').replace(repr(old),repr(intro)).replace('Preserve uniform quadrature and rearrangement proof gaps','Preserve normalized totient candidate for substantive review')
(P/'integrate.py').write_text(t)
