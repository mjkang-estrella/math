from pathlib import Path
import json
from fractions import Fraction as F
L=Path(__file__).resolve().parent
data=json.loads((L/'frozen/0018-boundary-result.json').read_text())
for line in sorted({tuple(f) for e in data['edges'] for f in e['lines']}):
 print(line)
 for e in data['edges']:
  if list(line) in e['lines']: print(e['endpoints'],e['residues'])
