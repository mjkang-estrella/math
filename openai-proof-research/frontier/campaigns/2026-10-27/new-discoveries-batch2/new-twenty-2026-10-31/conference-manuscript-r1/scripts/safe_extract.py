"""Safe extraction of a ZIP into a NEW empty directory (no Lean is run).
   python3 -I -B safe_extract.py ARCHIVE.zip DEST_DIR RECEIPT.json
Rejects absolute names, '..' components, backslashes, drive letters, duplicate names,
symlinks / non-regular members, encrypted members, and oversize members; verifies CRCs."""
import hashlib, json, os, stat, sys, zipfile
arc, dest, rec_path = sys.argv[1:4]
if os.path.lexists(dest):
    sys.exit(f'destination exists: {dest}')
MAX_MEMBER, MAX_TOTAL = 64 << 20, 512 << 20
h = hashlib.sha256(open(arc, 'rb').read()).hexdigest()
z = zipfile.ZipFile(arc)
names, total, members, problems = set(), 0, [], []
for i in z.infolist():
    n = i.filename
    mode = i.external_attr >> 16
    parts = n.split('/')
    if (n.startswith('/') or '\\' in n or ':' in parts[0] or any(p in ('..', '') for p in parts[:-1])
            or n in names or (i.flag_bits & 1) or i.file_size > MAX_MEMBER
            or (mode and stat.S_IFMT(mode) not in (0, stat.S_IFREG, stat.S_IFDIR))):
        problems.append(n)
    names.add(n)
    total += i.file_size
if total > MAX_TOTAL:
    problems.append('<total size>')
bad_crc = z.testzip()
if problems or bad_crc:
    sys.exit(f'UNSAFE: {problems} crc={bad_crc}')
os.makedirs(dest)
real = os.path.realpath(dest)
for i in z.infolist():
    if i.filename.endswith('/'):
        os.makedirs(os.path.join(dest, i.filename), exist_ok=True)
        continue
    target = os.path.realpath(os.path.join(dest, i.filename))
    assert target.startswith(real + os.sep), i.filename
    os.makedirs(os.path.dirname(target), exist_ok=True)
    data = z.read(i)
    with open(target, 'xb') as f:
        f.write(data)
    os.chmod(target, 0o644)
    members.append({'name': i.filename, 'size': i.file_size, 'sha256': hashlib.sha256(data).hexdigest()})
rec = {'archive': arc, 'archive_sha256': h, 'destination': dest, 'members': len(members), 'safe': True,
       'checks': 'no absolute/../backslash/drive names, no duplicates, regular files only, no encryption, '
                 'member <= 64 MiB, total <= 512 MiB, CRC verified, realpath containment, exclusive create',
       'files': members}
json.dump(rec, open(rec_path, 'w'), indent=1)
print('SAFE', len(members), 'members', h)
