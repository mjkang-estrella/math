"""Safely extract a dossier ZIP into a NEW directory.
Rejects absolute paths, '..' components, backslashes, symlinks, non-regular
members and duplicate names; never deletes or overwrites anything.
Usage: python3 -I safe_extract.py ARCHIVE.zip /absolute/new/destination"""
import pathlib, stat, sys, zipfile
archive = pathlib.Path(sys.argv[1]); dest = pathlib.Path(sys.argv[2]).resolve()
assert not dest.exists(), 'destination must be new'
with zipfile.ZipFile(archive) as z:
    names = set()
    for i in z.infolist():
        p = pathlib.PurePosixPath(i.filename)
        assert i.filename not in names, 'duplicate ' + i.filename
        names.add(i.filename)
        assert not p.is_absolute() and '..' not in p.parts and '\\' not in i.filename, i.filename
        mode = i.external_attr >> 16
        assert not stat.S_ISLNK(mode), 'symlink ' + i.filename
        assert i.is_dir() or mode == 0 or stat.S_ISREG(mode), 'non-regular ' + i.filename
    dest.mkdir(parents=True)
    for i in z.infolist():
        target = (dest / i.filename).resolve()
        assert target == dest or dest in target.parents, i.filename
        if i.is_dir():
            target.mkdir(parents=True, exist_ok=True)
            continue
        target.parent.mkdir(parents=True, exist_ok=True)
        with z.open(i) as src, open(target, 'xb') as out:
            out.write(src.read())
print(dest)
