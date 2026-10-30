from pathlib import Path
import shutil
r=Path(__file__).resolve().parent
d=r/'attempts';d.mkdir(exist_ok=True)
n=len(list(d.iterdir()));out=d/str(n);out.mkdir()
for p in (r/'logs').iterdir():shutil.copyfile(p,out/p.name)
for p in (r/'formal').glob('*.lean'):shutil.copyfile(p,out/p.name)
