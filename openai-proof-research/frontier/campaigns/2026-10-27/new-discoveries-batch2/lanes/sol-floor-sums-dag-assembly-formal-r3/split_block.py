from pathlib import Path
import re,sys,json,shutil
L=Path(__file__).resolve().parent;f=L/(sys.argv[1]+'.lean');s=f.read_text()
dest=L/'attempts'/f.stem;dest.mkdir(parents=True,exist_ok=True);shutil.copyfile(f,dest/'unsplit.lean')
for ext in ['log','console','guard.json']:
 p=L/'logs'/(f.stem+'.'+ext)
 if p.exists():shutil.copyfile(p,dest/('unsplit.'+ext))
header,rest=s.split('theorem ',1);parts=re.split(r'(?=theorem n\d+ )','theorem '+rest)
parts=[p for p in parts if p];D=L/'parts';D.mkdir(exist_ok=True);mods=[]
for k,p in enumerate(parts):
 p=p.removesuffix('end\nend Assembly\n');name=f'parts.{f.stem}_{k:03d}'
 hdr=header if k==0 else header.replace('import Dag167',f'import {mods[-1]}')
 if k and hdr==header:hdr=f'import {mods[-1]}\n'+header
 (L/(name.replace('.','/')+'.lean')).write_text(hdr+p+'end\nend Assembly\n');mods.append(name)
f.write_text(f'import {mods[-1]}\nset_option autoImplicit false\nset_option warningAsError true\n')
(L/(f.stem+'-parts.json')).write_text(json.dumps(mods,indent=2)+'\n')
print('split same composition block',f.stem,len(mods))
