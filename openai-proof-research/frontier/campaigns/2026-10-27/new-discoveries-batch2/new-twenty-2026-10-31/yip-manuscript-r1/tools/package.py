"""Build deterministic ZIPs.
  python3 -I tools/package.py source   -> source-manifest.json, source-only-proof.zip
  python3 -I tools/package.py full     -> dossier-manifest.json, full-dossier.zip, archive-hashes.json"""
import hashlib, json, pathlib, sys, zipfile
L = pathlib.Path(__file__).resolve().parents[1]
sha = lambda p: hashlib.sha256(p.read_bytes()).hexdigest()
SOURCE = ['proof/Yip355956.lean', 'proof/ReviewAudit.lean', 'proof/ReviewSanity.lean', 'PROOF.md', 'REPRODUCE.md',
          'pins.json', 'replay.py', 'safe_extract.py', 'diagnostic.py'] + sorted('sources/' + p.name for p in (L / 'sources').iterdir())
FULL_DIRS = ['evidence', 'qa', 'receipts', 'sources', 'proof', 'tools', 'fresh-extraction/replay-receipts']
FULL_TOP = ['paper.pdf', 'write_paper.py', 'paper-build.json', 'PROOF.md', 'REPRODUCE.md', 'SUMMARY.md', 'results.json',
            'pins.json', 'replay.py', 'safe_extract.py', 'diagnostic.py', 'source-manifest.json', 'source-only-proof.zip',
            'frozen-before.json', 'frozen-after.json', 'TASK.txt', 'launch.json']


def write_zip(path, names):
    with zipfile.ZipFile(path, 'w', zipfile.ZIP_DEFLATED) as z:
        for n in names:
            zi = zipfile.ZipInfo(n, date_time=(2026, 11, 1, 0, 0, 0))
            zi.external_attr = 0o100644 << 16
            zi.compress_type = zipfile.ZIP_DEFLATED
            z.writestr(zi, (L / n).read_bytes())


if sys.argv[1] == 'source':
    for n in SOURCE:
        assert (L / n).is_file() and not n.endswith('.olean'), n
    m = {n: sha(L / n) for n in SOURCE}
    (L / 'source-manifest.json').write_text(json.dumps(m, indent=1))
    write_zip(L / 'source-only-proof.zip', SOURCE + ['source-manifest.json'])
    print('source-only-proof.zip', sha(L / 'source-only-proof.zip'), len(SOURCE) + 1, 'members')
else:
    names = list(FULL_TOP)
    for d in FULL_DIRS:
        for p in sorted((L / d).rglob('*')):
            if p.is_file() and p.suffix != '.olean' and '__pycache__' not in p.parts:
                names.append(str(p.relative_to(L)))
    names = sorted(set(names))
    for n in names:
        assert (L / n).is_file(), n
    m = {n: sha(L / n) for n in names}
    (L / 'dossier-manifest.json').write_text(json.dumps(m, indent=1))
    write_zip(L / 'full-dossier.zip', names + ['dossier-manifest.json'])
    ah = {'source-only-proof.zip': sha(L / 'source-only-proof.zip'), 'full-dossier.zip': sha(L / 'full-dossier.zip'),
          'source-manifest.json': sha(L / 'source-manifest.json'), 'dossier-manifest.json': sha(L / 'dossier-manifest.json'),
          'full_members': len(names) + 1}
    (L / 'archive-hashes.json').write_text(json.dumps(ah, indent=1))
    print(json.dumps(ah, indent=1))
