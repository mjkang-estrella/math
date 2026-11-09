"""Build deterministic ZIPs.
  python3 -I tools/package.py source   -> source-manifest.json, source-only-proof.zip
  python3 -I tools/package.py full     -> dossier-manifest.json, full-dossier.zip, archive-hashes.json"""
import hashlib, json, pathlib, sys, zipfile
L = pathlib.Path(__file__).resolve().parents[1]
sha = lambda p: hashlib.sha256(p.read_bytes()).hexdigest()
SOURCE = ['proof/OrdinalLine.lean', 'proof/ReviewAudit.lean', 'proof/ReviewSanity.lean', 'PROOF.md', 'REPRODUCE.md',
          'pins.json', 'replay.py', 'safe_extract.py', 'diagnostic.py'] + sorted('sources/' + p.name for p in (L / 'sources').iterdir())
FULL_DIRS = ['evidence', 'qa', 'receipts', 'sources', 'proof', 'tools', 'fresh-extraction/replay-receipts']
FULL_TOP = ['paper.pdf', 'write_paper.py', 'paper-build.json', 'PROOF.md', 'REPRODUCE.md', 'SUMMARY.md', 'results.json',
            'pins.json', 'replay.py', 'safe_extract.py', 'diagnostic.py', 'source-manifest.json', 'source-only-proof.zip',
            'frozen-before.json', 'frozen-after.json', 'TASK.txt', 'launch.json']
EXCLUDE_SUFFIX = {'.olean', '.ilean', '.pyc'}
# Files allowed to MENTION 366834 names without containing 366834 material: the frozen-input
# bindings list every frozen path with its sha256 (paths and hashes only), and the two tools
# contain the screening strings themselves.
SCREEN_EXEMPT = {'frozen-before.json': 'path+sha256 bindings only', 'frozen-after.json': 'path+sha256 bindings only',
                 'tools/package.py': 'contains the screen strings', 'tools/assemble_evidence.py': 'contains the screen strings'}


def write_zip(path, names):
    with zipfile.ZipFile(path, 'w', zipfile.ZIP_DEFLATED) as z:
        for n in names:
            zi = zipfile.ZipInfo(n, date_time=(2026, 11, 1, 0, 0, 0))
            zi.external_attr = 0o100644 << 16
            zi.compress_type = zipfile.ZIP_DEFLATED
            z.writestr(zi, (L / n).read_bytes())


def screen(names):
    for n in names:
        assert (L / n).is_file() and not (L / n).is_symlink(), n
        assert pathlib.PurePosixPath(n).suffix not in EXCLUDE_SUFFIX, n
        if n.endswith(('.lean', '.md', '.json', '.py', '.txt', '.log', '.jsonl')) and n not in SCREEN_EXEMPT:
            t = (L / n).read_text(errors='replace')
            assert 'Caterpillar366834' not in t and 'CaterpillarCenter' not in t, '366834 material in ' + n


if sys.argv[1] == 'source':
    screen(SOURCE)
    m = {n: sha(L / n) for n in SOURCE}
    (L / 'source-manifest.json').write_text(json.dumps(m, indent=1))
    write_zip(L / 'source-only-proof.zip', SOURCE + ['source-manifest.json'])
    print('source-only-proof.zip', sha(L / 'source-only-proof.zip'), len(SOURCE) + 1, 'members')
else:
    names = list(FULL_TOP)
    for d in FULL_DIRS:
        for p in sorted((L / d).rglob('*')):
            if p.is_file() and p.suffix not in EXCLUDE_SUFFIX and '__pycache__' not in p.parts:
                names.append(str(p.relative_to(L)))
    names = sorted(set(names))
    screen(names)
    m = {n: sha(L / n) for n in names}
    (L / 'dossier-manifest.json').write_text(json.dumps(m, indent=1))
    write_zip(L / 'full-dossier.zip', names + ['dossier-manifest.json'])
    ah = {'source-only-proof.zip': sha(L / 'source-only-proof.zip'), 'full-dossier.zip': sha(L / 'full-dossier.zip'),
          'source-manifest.json': sha(L / 'source-manifest.json'), 'dossier-manifest.json': sha(L / 'dossier-manifest.json'),
          'full_members': len(names) + 1, 'screen_exemptions': SCREEN_EXEMPT}
    (L / 'archive-hashes.json').write_text(json.dumps(ah, indent=1))
    print(json.dumps(ah, indent=1))
