from pathlib import Path
import zipfile
root=Path(__file__).resolve().parents[1]
with zipfile.ZipFile(root.parent/'expanded-corpus-r234/proof-packet-v2.zip') as z:
 for m in z.infolist():
  assert m.filename in {'Hurlbert.lean','AllAxioms.lean','Inventory.lean'} and m.file_size<1000000
  p=root/'replay'/m.filename
  with p.open('xb') as f:f.write(z.read(m))
