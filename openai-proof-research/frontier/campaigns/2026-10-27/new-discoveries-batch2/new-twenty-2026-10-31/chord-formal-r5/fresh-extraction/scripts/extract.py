from pathlib import Path,PurePosixPath
import zipfile
root=Path(__file__).resolve().parent.parent
out=root/'fresh-extraction'
out.mkdir(exist_ok=False)
with zipfile.ZipFile(root/'chord5-source.zip') as z:
 for n in z.namelist():
  p=PurePosixPath(n)
  assert not p.is_absolute() and '..' not in p.parts
 z.extractall(out)
 for item in z.infolist():
  mode=(item.external_attr>>16)
  if mode: (out/item.filename).chmod(mode)
print('Fresh source extraction:',out)
