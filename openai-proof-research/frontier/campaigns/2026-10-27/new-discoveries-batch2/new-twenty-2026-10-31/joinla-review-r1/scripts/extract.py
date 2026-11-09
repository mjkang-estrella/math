import tarfile,pathlib,hashlib
root=pathlib.Path(__file__).resolve().parents[1]
packet=root.parent/'expanded-corpus-r159/lean-packet.tar'
assert hashlib.sha256(packet.read_bytes()).hexdigest()=='a68ba4bde2e1f3dabacc336c30848ba0ed4a1f701e3df98e68d12eaf6bdd31aa'
dest=root/'replay'
assert not list(dest.iterdir())
with tarfile.open(packet) as t:
 for m in t:
  p=pathlib.PurePosixPath(m.name)
  assert not p.is_absolute() and '..' not in p.parts and m.isfile()
  out=dest/p
  out.parent.mkdir(parents=True,exist_ok=True)
  out.write_bytes(t.extractfile(m).read())
  print(m.name,m.size,hashlib.sha256(out.read_bytes()).hexdigest())
