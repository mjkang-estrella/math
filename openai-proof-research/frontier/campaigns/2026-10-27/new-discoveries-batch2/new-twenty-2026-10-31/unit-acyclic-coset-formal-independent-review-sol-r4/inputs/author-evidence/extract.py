from pathlib import Path
import shutil,json,hashlib
lane=Path(__file__).resolve().parent
clean=lane/'cleanroom'
assert not list(clean.rglob("*.olean"))
(lane/"results").mkdir(exist_ok=True)
(clean/'src').mkdir(parents=True,exist_ok=True)
(clean/'build').mkdir(exist_ok=True)
(clean/'audit').mkdir(exist_ok=True)
files=[*lane.joinpath('src').glob('*.lean'),*lane.joinpath('audit').glob('*.lean')]
files += [lane/n for n in ['runner.py','env.sh','check.sh','checker.sh','audit.sh','run_negative.sh','write_lane.py']]
records=[]
for p in files:
    rel=p.relative_to(lane);dst=clean/rel
    dst.parent.mkdir(parents=True,exist_ok=True)
    shutil.copyfile(p,dst)
    sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
    assert sha(p)==sha(dst)
    records.append({'path':str(rel),'sha256':sha(dst)})
pins={'lean':'4.34.1','mathlib':'d13f23b723b8a846827a245b89c10fc7d3f11612','production_modules':['Matching','Bridges','Coset','Controls','Sequence']}
(lane/'results'/'generated-build-plan.json').write_text(json.dumps(pins,indent=2))
(clean/'generated-build-plan.json').write_text(json.dumps(pins,indent=2))
record={'files':records,'initial_build_entries':list((clean/'build').iterdir()),'copied_oleans':False,'source_only':True,'path_policy':'cleanroom/build plus pinned upstream package lib/lean directories ONLY; env.sh recomputes LANE from cleanroom'}
(lane/'results'/'extraction.json').write_text(json.dumps(record,indent=2))
