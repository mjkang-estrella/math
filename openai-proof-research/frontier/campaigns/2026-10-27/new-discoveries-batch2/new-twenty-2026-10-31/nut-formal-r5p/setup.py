from pathlib import Path
import hashlib,json,shutil
root=Path(__file__).resolve().parent;base=root.parent
selected=[]
for lane in ['nut-formal-r4b','nut-formal-r3b']:
 p=base/lane
 if lane.endswith('r4b'):
  selected += [x for x in (p/'formal').glob('*.lean')]
  selected += [x for x in (p/'scripts').rglob('*') if x.is_file()]
  selected += [x for x in p.glob('*.json')]+[p/n for n in ['SUMMARY.md','GAPS.md','statement-correspondence.md','replay.py','replay_r4.py','nut-r4b-source.zip']]
 else:
  selected += [p/'GAPS.md']+[x for x in (p/'scripts').rglob('*') if x.is_file()]
selected += [base/'nut-formal-r2'/n for n in ['all-normalized-certificates.json','PART-B-DESIGN.md']]
selected += [base/'nut-interface-r5/NutInterface.lean']
selected += list((base/'nut-formal-r4a/formal').glob('*.lean'))
selected += list((base/'nut-formal-r4a').glob('*.zip'))
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
manifest={str(p.relative_to(base)):sha(p) for p in sorted(set(selected))}
(root/'inputs-before.json').write_text(json.dumps(manifest,indent=2)+'\n')
assert manifest['nut-formal-r4b/nut-r4b-source.zip']=='4b632a6f860f063c40ad1d2500c59764c578b0999f03187c910cedd7f72f3ba7'
assert manifest['nut-interface-r5/NutInterface.lean']=='632b6913be638de9470b917bc4ec860291192ee552a6e7f1b5d4eb913d5ebcff'
for p in selected:
 dest=root/'inputs'/p.relative_to(base);dest.parent.mkdir(parents=True,exist_ok=True);shutil.copyfile(p,dest);assert sha(p)==sha(dest)
formal=root/'formal';formal.mkdir(exist_ok=True)
for p in (base/'nut-formal-r4b/formal').glob('*.lean'):shutil.copyfile(p,formal/p.name)
shared=[];added=[]
for p in (base/'nut-formal-r4a/formal').glob('*.lean'):
 dest=formal/p.name
 if dest.exists():
  assert sha(p)==sha(dest),p.name
  shared.append(p.name)
 else:shutil.copyfile(p,dest);added.append(p.name)
shutil.copyfile(base/'nut-interface-r5/NutInterface.lean',formal/'NutInterface.lean')
(root/'r4a-compatibility.json').write_text(json.dumps({'shared_identical':shared,'added_identical':added},indent=2)+'\n')
shutil.copytree(base/'nut-formal-r4b/scripts',root/'scripts',dirs_exist_ok=True)
for n in ['modules.json','replay_r4.py']:shutil.copyfile(base/'nut-formal-r4b'/n,root/n)
print('copied',len(manifest),'inputs; r4a added',added)
