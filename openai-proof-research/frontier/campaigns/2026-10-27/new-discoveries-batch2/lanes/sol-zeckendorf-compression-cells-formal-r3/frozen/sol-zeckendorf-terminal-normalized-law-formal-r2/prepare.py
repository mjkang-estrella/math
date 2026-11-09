from pathlib import Path
import shutil
L=Path(__file__).resolve().parent
(L/'failures').mkdir(exist_ok=True)
if (L/'Law.lean').exists():shutil.move(L/'Law.lean',L/'failures/PMFLaw.lean')
for n in ['lake-manifest.json','lean-toolchain']:
 shutil.copyfile(L.parent/'sol-zeckendorf-literal-game-law-formal-r1/administrative'/n,L/'administrative'/n)
