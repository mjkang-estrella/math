"""One-shot own-root seal. Does not assign mathematical gates."""
import hashlib,json
from pathlib import Path
R=Path('frontier/campaigns/2026-10-14/fresh-analytic-discovery-r157')
assert Path.cwd().resolve()==Path('/home/mj-kang/Documents/Dev/math/openai-proof-research')
assert not (R/'MANIFEST.json').exists(), 'refuse reseal'
assert (R/'FINAL.md').is_file() and (R/'REPORT.md').is_file()
outside={'FINAL.md','MANIFEST.json','REPORT.md'}
rows=[]
for p in sorted(R.rglob('*')):
    assert not p.is_symlink(), 'symlink'
    if p.is_dir():continue
    assert p.is_file()
    rel=p.relative_to(R).as_posix()
    if rel in outside:continue
    b=p.read_bytes();rows.append({'path':rel,'size':len(b),'sha256':hashlib.sha256(b).hexdigest()})
(R/'MANIFEST.json').write_text(json.dumps({'schema':'r157-exact-selected-members-v1','excluded_root_envelopes':sorted(outside),'files':rows},indent=2)+'\n')
for name in sorted(outside): print(name,hashlib.sha256((R/name).read_bytes()).hexdigest())
print('payload',len(rows))
