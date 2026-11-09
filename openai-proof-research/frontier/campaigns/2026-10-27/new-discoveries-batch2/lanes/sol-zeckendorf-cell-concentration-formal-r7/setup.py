from pathlib import Path
import json,hashlib
L=Path(__file__).resolve().parent
for p in (L/'inherited').glob('*.lean'):
 if p.stem not in ['Inventory','Audit']: (L/p.name).write_bytes(p.read_bytes())
for name in ['runner.py','pins.json','run.sh']:(L/name).write_bytes((L/'inherited'/name).read_bytes())
for name in ['Inventory.lean','Audit.lean']:
 s=(L/'inherited'/name).read_text().replace('import Tail','import Concentration')
 if name=='Inventory.lean':s=s.replace('modName == `Tail)', 'modName == `Tail || modName == `Concentration)')
 else:s=s.replace('`Abundance, `Tail]', '`Abundance, `Tail, `Concentration]')
 (L/name).write_text(s)
print('setup complete')
