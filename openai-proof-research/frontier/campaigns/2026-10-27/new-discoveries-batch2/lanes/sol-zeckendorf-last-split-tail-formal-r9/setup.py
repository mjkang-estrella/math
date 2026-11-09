from pathlib import Path
import json
L=Path(__file__).resolve().parent
S=L/'frozen/sol-zeckendorf-concentration-assembly-formal-r8'
for n in ['Literal','Terminal','Law','Cells','Product','Prefix','Marks','Boards','Injection','Abundance','Tail','Concentration','Assembly']:
 (L/(n+'.lean')).write_bytes((S/(n+'.lean')).read_bytes())
for f in ['runner.py','pins.json']:(L/f).write_bytes((S/f).read_bytes())
for f in ['Inventory.lean','Audit.lean']:
 t=(S/f).read_text().replace('import Assembly','import LastSplit')
 t=t.replace('modName == `Assembly)', 'modName == `Assembly || modName == `LastSplit)')
 t=t.replace('`Concentration, `Assembly]', '`Concentration, `Assembly, `LastSplit]')
 (L/f).write_text(t)
(L/'run.sh').write_text((S/'run.sh').read_text().replace('Assembly;','Assembly LastSplit;'))
print('13 modules preserved; harness extended')
