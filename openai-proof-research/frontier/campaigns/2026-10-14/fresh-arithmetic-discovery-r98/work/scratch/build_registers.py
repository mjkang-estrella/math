import json, hashlib, pathlib
ROOT = pathlib.Path('.').resolve()
PK = ROOT / 'packet'
PIN = 'fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb'
RAW = 'https://raw.githubusercontent.com/openai/math/' + PIN + '/'
tree = json.loads((ROOT.parents[3] / 'sources/preprints-tree.json').read_text())
entries = {e['path']: e for e in tree['tree']}
log = [json.loads(l) for l in (PK / 'public/fetch-log.jsonl').read_text().splitlines()]
MODP = 'preprints/Reconstruction-from-Milnor-K-theory-modulo-the-characteristic-October-5-2026/build/build/'
keep = {MODP + 'main.tex': 'read in full (r98)',
        MODP + 'sections/01-introduction.tex': 'read in full (r98)',
        MODP + 'sections/02-symbols.tex': 'read in full (r98)',
        MODP + 'sections/05-fields.tex': 'read in full (r98)'}
uses = {MODP + 'main.tex': 'abstract/structure',
        MODP + 'sections/01-introduction.tex': 'V_F, R_F, W_F, compatibility, thm:main',
        MODP + 'sections/02-symbols.tex': 'lem:p-basis, lem:zero-symbol, lem:affine-symbol',
        MODP + 'sections/05-fields.tex': 'prop:projective-lift and multiplicativity step in proof of thm:main (comparison)'}
extent = {
 'Lechs-multiplicity-conjecture-September-23-2026/build/main.tex': 'read during family screening (extent not re-verified after context summary)',
 'Lechs-multiplicity-conjecture-September-23-2026/build/sections/charp.tex': 'read during family screening (extent not re-verified after context summary)',
 'The-Bogomolov-Pop-reconstruction-theorem-September-23-2026/build/local-theory.tex': 'lines 1-180 read',
}
retained, removed = [], []
for x in log:
    p = x['path']
    e = entries[p]
    assert e['sha'] == x['git_blob'] and e['size'] == x['size'] and x['match']
    rec = {'upstream_path': p, 'git_blob': x['git_blob'], 'size': x['size'], 'sha256': x['sha256'], 'raw_url': RAW + p}
    if p in keep:
        rec.update({'local': 'private/upstream/' + p, 'read_extent': keep[p], 'used_for': uses[p]})
        retained.append(rec)
    else:
        short = p.split('preprints/', 1)[1]
        rec.update({'read_extent': extent.get(short, 'not read in r98 (fetched for screening; body not used)'),
                    'reason': 'fetched during screening; not used by the r98 derivations; local copy deleted before sealing'})
        removed.append(rec)
reg = {'pin': PIN, 'tree_path': 'sources/preprints-tree.json', 'tree_sha256': hashlib.sha256((ROOT.parents[3] / 'sources/preprints-tree.json').read_bytes()).hexdigest(),
       'tree_entries': len(entries), 'truncated': tree.get('truncated', False), 'retained': retained, 'removed': removed}
(PK / 'public/source-register.json').write_text(json.dumps(reg, indent=1) + '\n')
for r in removed:
    (PK / 'private/upstream' / r['upstream_path']).unlink()
# prune empty dirs
for d in sorted((PK / 'private/upstream').rglob('*'), key=lambda q: -len(q.parts)):
    if d.is_dir() and not any(d.iterdir()):
        d.rmdir()
print(len(retained), len(removed))
