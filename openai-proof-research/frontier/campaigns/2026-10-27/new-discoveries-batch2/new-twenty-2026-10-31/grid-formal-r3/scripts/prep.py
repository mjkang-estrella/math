from pathlib import Path
p=Path(__file__).resolve().parent.parent
pkg=Path('/home/mj-kang/Documents/Dev/math/openai-proof-research/frontier/campaigns/2026-10-14/formal/.lake/packages')
(p/'build').mkdir(exist_ok=True)
for base in pkg.glob('*/.lake/build/lib/lean'):
 for f in base.rglob('*'):
  if f.is_file():
   d=p/'build'/f.relative_to(base)
   if not d.exists():
    d.parent.mkdir(parents=True,exist_ok=True)
    d.symlink_to(f)
attr=p/'build/Mathlib/Tactic/Bound/Attribute.olean'
for f in attr.parent.glob(attr.name+'*'):
 if f.is_symlink(): f.unlink()
