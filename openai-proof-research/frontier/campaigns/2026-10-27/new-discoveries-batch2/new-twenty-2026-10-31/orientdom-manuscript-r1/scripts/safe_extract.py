from pathlib import Path,PurePosixPath
import zipfile,hashlib,stat,json,sys
R=Path.cwd(); p=R/'Lean-packet.zip'; target=R/(sys.argv[1] if len(sys.argv)>1 else 'tmp/packet-retest')
assert target.resolve().is_relative_to(R.resolve())
assert not target.exists(),'Use a fresh destination inside the dossier'
hash=hashlib.sha256(p.read_bytes()).hexdigest(); assert hash=='3d9361bef2cc188b191519cd9718e4d983ccbe6b17df8dec6448dcf5228ab1d6'
target.mkdir(parents=True); members=[]
with zipfile.ZipFile(p) as z:
 infos=z.infolist(); assert sum(i.file_size for i in infos)<64*1024**2
 assert len({i.filename for i in infos})==len(infos)
 for i in infos:
  q=PurePosixPath(i.filename); mode=i.external_attr>>16
  assert not q.is_absolute() and '..' not in q.parts and '\\' not in i.filename and not stat.S_ISLNK(mode)
  assert stat.S_IFMT(mode) in [0,stat.S_IFREG,stat.S_IFDIR]
  dest=target/i.filename; assert dest.resolve().is_relative_to(target.resolve())
  if i.is_dir(): dest.mkdir(parents=True,exist_ok=True); continue
  dest.parent.mkdir(parents=True,exist_ok=True); b=z.read(i); dest.write_bytes(b)
  original=R/'packet-safe-extraction'/i.filename
  assert b==original.read_bytes()
  members.append(dict(path=i.filename,bytes=len(b),sha256=hashlib.sha256(b).hexdigest()))
(R/'receipts/packet-retest.json').write_text(json.dumps(dict(status='PASS',packet_sha256=hash,members=members,executed_code=False),indent=2)+'\n')
print('PASS safe extraction:',len(members),'members; byte-identical; no code executed')
