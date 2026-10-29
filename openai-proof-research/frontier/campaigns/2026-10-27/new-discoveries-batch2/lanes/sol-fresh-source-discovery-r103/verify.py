from pathlib import Path
import hashlib,json
P=Path(__file__).resolve().parent
for name in ['sourcebytes.sha256','manifest.sha256']:
 rows=(P/name).read_text().splitlines()
 for row in rows:
  h,f=row.split('  ',1);assert hashlib.sha256((P/f).read_bytes()).hexdigest()==h,f
 print(name,len(rows),'PASS')
assert not (P/'PROOF.md').exists()
assert json.loads((P/'provenance.json').read_text())['credit']==0
assert not json.loads((P/'fisher-full-screen.json').read_text())['failures']
print('Zero credit, no PROOF.md, corrected complete-corpus exact screen PASS')
