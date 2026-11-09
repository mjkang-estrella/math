"""Safe extraction of a dossier ZIP into a new empty directory.

    python3 -I safe_extract.py ARCHIVE.zip NEW_DIR RECEIPT.json

Rejects absolute paths, '..' components, backslashes, symlinks, duplicate names, device files,
build artefacts (.olean/.ilean/.c), more than 2000 members and members over 64 MiB; writes regular
files only (mode 0644) and records the SHA-256 of every member.
"""
import datetime, hashlib, json, stat, sys, zipfile
from pathlib import Path, PurePosixPath


def main():
    arc, dest, receipt = Path(sys.argv[1]), Path(sys.argv[2]), Path(sys.argv[3])
    if dest.exists():
        sys.exit(f'refusing: {dest} exists')
    with zipfile.ZipFile(arc) as z:
        infos = z.infolist()
        names = [i.filename for i in infos]
        assert len(infos) <= 2000 and len(set(names)) == len(names), 'too many or duplicate members'
        for i in infos:
            p = PurePosixPath(i.filename)
            mode = i.external_attr >> 16
            assert not p.is_absolute() and '..' not in p.parts and '\\' not in i.filename, i.filename
            assert not stat.S_ISLNK(mode) and (mode == 0 or stat.S_ISREG(mode) or stat.S_ISDIR(mode)), i.filename
            assert i.file_size <= 64 * 2 ** 20, i.filename
            assert p.suffix not in ('.olean', '.ilean', '.c'), i.filename
        dest.mkdir(parents=True)
        members = {}
        for i in infos:
            if i.is_dir():
                continue
            data = z.read(i)
            t = dest.joinpath(*PurePosixPath(i.filename).parts)
            assert dest.resolve() in t.resolve().parents
            t.parent.mkdir(parents=True, exist_ok=True)
            t.write_bytes(data)
            t.chmod(0o644)
            members[i.filename] = hashlib.sha256(data).hexdigest()
    rec = {'utc': datetime.datetime.now(datetime.timezone.utc).isoformat(), 'archive': str(arc.resolve()),
           'archive_sha256': hashlib.sha256(arc.read_bytes()).hexdigest(), 'destination': str(dest.resolve()),
           'num_members': len(members), 'members': members}
    receipt.write_text(json.dumps(rec, indent=1))
    print(len(members), rec['archive_sha256'])


if __name__ == '__main__':
    main()
