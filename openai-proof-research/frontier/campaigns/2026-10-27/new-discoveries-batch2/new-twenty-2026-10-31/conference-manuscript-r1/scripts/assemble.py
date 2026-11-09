"""Assemble manifests and deterministic ZIPs.
   python3 -I -B scripts/assemble.py source   -> dossier/MANIFEST.json, conference-324342-source.zip, source-manifest.json
   python3 -I -B scripts/assemble.py full     -> conference-324342-full-dossier.zip, full-dossier-manifest.json"""
import hashlib, json, os, sys, zipfile
sha = lambda b: hashlib.sha256(b).hexdigest()


def files_under(root):
    out = []
    for d, ds, fs in os.walk(root):
        ds.sort()
        for f in sorted(fs):
            p = os.path.join(d, f)
            assert not os.path.islink(p), p
            out.append(p)
    return out


def write_zip(path, members):  # members: list of (arcname, filesystem path)
    names = [a for a, _ in members]
    assert len(names) == len(set(names))
    with zipfile.ZipFile(path + '.part', 'w', zipfile.ZIP_DEFLATED, compresslevel=9) as z:
        for arc, p in sorted(members):
            zi = zipfile.ZipInfo(arc, date_time=(1980, 1, 1, 0, 0, 0))
            zi.external_attr = 0o100644 << 16
            zi.compress_type = zipfile.ZIP_DEFLATED
            z.writestr(zi, open(p, 'rb').read())
    os.replace(path + '.part', path)
    return [{'name': a, 'bytes': os.path.getsize(p), 'sha256': sha(open(p, 'rb').read())} for a, p in sorted(members)]


mode = sys.argv[1]
if mode == 'source':
    dossier = [p for p in files_under('dossier') if not p.endswith('MANIFEST.json')]
    man = [{'path': os.path.relpath(p, 'dossier'), 'bytes': os.path.getsize(p), 'sha256': sha(open(p, 'rb').read())}
           for p in dossier]
    json.dump({'mathdb_id': 324342, 'status': 'DRAFT dossier; zero accepted credit', 'files': len(man), 'entries': man},
              open('dossier/MANIFEST.json', 'w'), indent=1)
    keep = ('PROOF.md', 'REPRODUCE.md', 'MANIFEST.json', 'paper/', 'lean/', 'tools/', 'data/', 'mathdb/')
    members = [(os.path.relpath(p, 'dossier'), p) for p in files_under('dossier')
               if os.path.relpath(p, 'dossier').startswith(keep)]
    m = write_zip('conference-324342-source.zip', members)
    rec = {'archive': 'conference-324342-source.zip', 'sha256': sha(open('conference-324342-source.zip', 'rb').read()),
           'members': len(m), 'deterministic': 'sorted names, fixed 1980-01-01 timestamps, mode 0644, deflate level 9',
           'entries': m}
    json.dump(rec, open('source-manifest.json', 'w'), indent=1)
    print('source zip', rec['members'], 'members', rec['sha256'])
elif mode == 'full':
    members = [(p, p) for p in files_under('dossier')]
    # receipts of the calls that build or verify this ZIP are written after it and stay outside it
    members += [(p, p) for d in ('qa', 'receipts', 'scripts') for p in files_under(d)
                if not os.path.basename(p).startswith(('assemble-full.', 'verify-full'))]
    members += [(p, p) for p in ('conference-324342-draft.pdf', 'conference-324342-source.zip', 'source-manifest.json',
                                 'TASK.txt', 'launch.json')]
    m = write_zip('conference-324342-full-dossier.zip', members)
    rec = {'archive': 'conference-324342-full-dossier.zip',
           'sha256': sha(open('conference-324342-full-dossier.zip', 'rb').read()), 'members': len(m),
           'excluded': 'receipts/calls/assemble-full.* and verify-full*, SUMMARY.md, results.json, ARCHIVES-SHA256.json, full-dossier-manifest.json and '
                       'full-dossier-verification.json describe this ZIP and are outside it; tmp/ is scratch',
           'entries': m}
    json.dump(rec, open('full-dossier-manifest.json', 'w'), indent=1)
    print('full zip', rec['members'], 'members', rec['sha256'])
