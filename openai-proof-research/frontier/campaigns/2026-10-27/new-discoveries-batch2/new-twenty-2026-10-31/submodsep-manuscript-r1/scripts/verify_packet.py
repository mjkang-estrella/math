from pathlib import Path
import zipfile,hashlib,stat
L=Path(__file__).resolve().parents[1];p=L/'lean-packet.zip'
H=lambda b:hashlib.sha256(b).hexdigest()
assert H(p.read_bytes())=='441cb79ec825366931cdee6221b99e4b3235dd2145f343565e8df2fb2bd13db8'
seen=set();total=0
with zipfile.ZipFile(p) as z:
 for x in z.infolist():
  q=Path(x.filename);assert not q.is_absolute() and '..' not in q.parts and '\\' not in x.filename
  assert x.filename not in seen;seen.add(x.filename);assert not stat.S_ISLNK(x.external_attr>>16)
  total+=x.file_size;assert total<256*1024**2
  assert H(z.read(x))==H((L/'packet-safe'/q).read_bytes())
print('Packet hash, safety and extracted-byte correspondence PASS;',len(seen),'members')
