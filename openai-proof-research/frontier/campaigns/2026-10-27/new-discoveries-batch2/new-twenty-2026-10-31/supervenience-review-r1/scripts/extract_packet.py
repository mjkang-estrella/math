from pathlib import Path
import zipfile,hashlib,json
D=Path(__file__).resolve().parents[1];packet=D.parent/'expanded-corpus-r84/hierarchy-packet.zip';dest=D/'replay-extracted'
assert not dest.exists(), 'Use a fresh extraction destination; do not overwrite an audit'
with zipfile.ZipFile(packet) as z:
 assert sum(i.file_size for i in z.infolist())<1000000
 for i in z.infolist():
  p=Path(i.filename)
  assert not p.is_absolute() and '..' not in p.parts and ((i.external_attr>>16)&0o170000)!=0o120000
 z.extractall(dest)
print(json.dumps({'destination':str(dest),'packet_sha256':hashlib.sha256(packet.read_bytes()).hexdigest()}))
