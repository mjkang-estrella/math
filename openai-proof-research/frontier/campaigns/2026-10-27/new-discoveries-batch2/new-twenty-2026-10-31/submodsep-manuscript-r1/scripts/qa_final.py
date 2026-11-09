from pathlib import Path
import shutil
L=Path(__file__).resolve().parents[1]
for i in range(1,7):shutil.copy2(L/f'qa/page-{i}.png',L/f'qa/final-page-{i}.png')
