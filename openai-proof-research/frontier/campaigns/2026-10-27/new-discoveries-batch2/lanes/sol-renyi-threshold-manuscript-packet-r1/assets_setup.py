from pathlib import Path
import shutil,json,hashlib
R=Path(__file__).resolve().parent
A=R/'packet/assets';A.mkdir(exist_ok=True)
for p in ['/usr/share/fonts/liberation-serif-fonts/LiberationSerif-Regular.ttf','/usr/share/fonts/gdouros-symbola/Symbola.ttf']:
 shutil.copy2(p,A/Path(p).name)
print('Font assets copied')
