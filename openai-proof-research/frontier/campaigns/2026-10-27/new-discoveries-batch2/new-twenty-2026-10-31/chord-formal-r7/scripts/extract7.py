from pathlib import Path,PurePosixPath
import zipfile,stat
root=Path(__file__).resolve().parent.parent
out=root/'fresh-extraction'
out.mkdir(exist_ok=False)
with zipfile.ZipFile(root/'chord7-source.zip') as z:
    for item in z.infolist():
        p=PurePosixPath(item.filename)
        assert not p.is_absolute() and '..' not in p.parts
        assert not stat.S_ISLNK(item.external_attr>>16)
    z.extractall(out)
    for item in z.infolist():
        mode=item.external_attr>>16
        if mode: (out/item.filename).chmod(mode)
print(out)
