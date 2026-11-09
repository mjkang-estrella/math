from pathlib import Path
import hashlib
L=Path(__file__).resolve().parents[1]
for row in (L/'MANIFEST.sha256').read_text().splitlines():
 h,n=row.split('  ',1);p=L/n;assert p.resolve().is_relative_to(L)
 assert hashlib.sha256(p.read_bytes()).hexdigest()==h,n
print('All payload hashes PASS')
