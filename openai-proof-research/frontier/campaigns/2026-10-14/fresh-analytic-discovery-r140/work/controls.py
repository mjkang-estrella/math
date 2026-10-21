"""Small synthetic copied controls; never mutate or reseal an original input."""
from pathlib import Path
import sys,json,shutil,hashlib
R=Path(__file__).resolve().parents[1];sys.path.insert(0,str(R))
from verify import inventory,verify,OUTSIDE,digest
base=R/'private/controls';base.mkdir(exist_ok=False);seed=base/'seed';seed.mkdir();(seed/'note.txt').write_text('Synthetic control payload, not incoming research.\n')
(seed/'FINAL.md').write_text('Synthetic final\n');(seed/'REPORT.md').write_text('Synthetic report\n')
files,dirs=inventory(seed);(seed/'MANIFEST.json').write_text(json.dumps(dict(files={k:v for k,v in files.items() if k not in OUTSIDE},directories=dirs,outside=sorted(OUTSIDE)),sort_keys=True))
anchors={n:digest((seed/n).read_bytes()) for n in OUTSIDE};results=[]
for name in ['clean','changed','missing','extra-hidden','wrong-anchor','restored']:
    case=base/name;shutil.copytree(seed,case);a=dict(anchors)
    if name in ['changed','restored']:(case/'note.txt').write_text('changed\n')
    if name=='restored':shutil.copyfile(seed/'note.txt',case/'note.txt')
    if name=='missing':(case/'note.txt').unlink()
    if name=='extra-hidden':(case/'.extra').write_text('extra')
    if name=='wrong-anchor':a['FINAL.md']='0'*64
    before=inventory(case)
    try:verify(case,a);ok=True;detail='accepted'
    except (ValueError,FileNotFoundError) as e:ok=False;detail=str(e)
    assert before==inventory(case),'verifier wrote to fixture'
    assert ok==(name in ['clean','restored'])
    results.append(dict(case=name,accepted=ok,readonly=True,detail=detail))
(R/'control-results.json').write_text(json.dumps({'synthetic_only':True,'cases':results},indent=2));print(json.dumps(results))
