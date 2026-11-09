from pathlib import Path
p=Path(__file__).resolve().parent.parent
body=(p/'src/Audit2.lean').read_text().split('open Lean Elab Command\n',1)[1]
new=['GridFiniteCodes','GridExceptionalPartitions','GridExceptionalTwo','GridExceptionalCounts','GridExceptionalCountTwo','GridExceptionalSubgroups','GridExceptional','GridFreePaths','GridFinal3']
body=body.replace('`GridTransport, `GridFinal2]', '`GridTransport, `GridFinal2, '+', '.join('`'+n for n in new)+']')
body=body.replace('insert `GridFinal2','insert `GridFinal3').replace('#print axioms GridFinal2.mathdb_343536','#print axioms GridFinal3.mathdb_343536\n#print axioms Grid343536.exceptional_no_iso')
imports=(p/'inventory-modules.txt').read_text().splitlines()
(p/'src/Audit3.lean').write_text('module\n'+''.join('import all '+n+'\n' for n in imports)+'open Lean Elab Command\n'+body)
