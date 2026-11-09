from pathlib import Path
import hashlib, json, re, zipfile

root = Path(__file__).resolve().parent
fresh = root / 'fresh'
sha = lambda p: hashlib.sha256(p.read_bytes()).hexdigest()
bindings = json.loads((root / 'bindings.json').read_text())
for row in bindings:
    assert sha(Path(row['original'])) == sha(root / row['copy']) == row['sha256']
source = Path(bindings[0]['original']).parent
manifest = json.loads((root / 'frozen/MANIFEST.json').read_text())
for name, digest in manifest.items():
    assert sha(source / name) == digest, name
steps = [json.loads(p.read_text()) for p in sorted(fresh.glob('attempt-*.json'))]
assert len(steps) == 25
assert all(s['exit'] == 0 and s['reason'] is None and s['serial'] for s in steps)
assert all('-j1' in s['command'] and '-M2700' in s['command'] for s in steps)
namespace = {'__file__': str(fresh / 'certify.py')}
exec((fresh / 'certify.py').read_text().split('mode=sys.argv[1]')[0], namespace)
assert len(namespace['pins']()) == 9
log = (fresh / 'attempt-024.log').read_text()
names = namespace['inventory'](log)
audit = namespace['audit'](log, names)
assert len(names) == 986
origins = set(re.findall(r'^OWN_MODULE \S+ (\S+)$', log, re.M))
assert origins == set(namespace['MODULES']) and len(origins) == 24
assert int(re.search(r'TRANSITIVE_SAFE_COUNT (\d+)', log)[1]) == 20133
hashes = json.loads((fresh / 'archive-files.json').read_text())
assert all(sha(fresh / n) == h for n, h in hashes.items())
with zipfile.ZipFile(root / 'rebuilt-source-only.zip', 'w') as z:
    for name in list(hashes) + ['archive-files.json']:
        info = zipfile.ZipInfo(name, date_time=(2026, 10, 30, 0, 0, 0))
        info.compress_type = zipfile.ZIP_DEFLATED
        info.external_attr = 0o100644 << 16
        z.writestr(info, (fresh / name).read_bytes())
assert sha(root / 'rebuilt-source-only.zip') == sha(root / 'frozen/source-only.zip')
removed = []
for p in fresh.rglob('*'):
    if p.is_file() and p.suffix in {'.olean', '.ilean', '.ir', '.o', '.so', '.pyc'}:
        removed.append(str(p.relative_to(root)))
        p.unlink()
result = dict(status='PASS', modules=24, owned_declarations=986,
              transitive_constants=20133, compiler_calls=25, package_pins=9,
              archive_byte_identical=True, original_manifest_files=len(manifest),
              compiled_objects_removed=removed, steps=steps,
              scope='Independent root mechanical replay and supplied audit execution; '
                    'not independent mathematical/source/novelty adjudication',
              credit_added=0)
(root / 'root-replay-receipt.json').write_text(json.dumps(result, indent=2)+'\n')
(root / 'owned-audit.json').write_text(json.dumps(audit, indent=2)+'\n')
print(json.dumps({k:v for k,v in result.items() if k not in {'steps','compiled_objects_removed'}}))
