from pathlib import Path
import sys,json
sys.path.insert(0,str(Path(__file__).resolve().parent))
from fetch_sources import P,get
jobs=[('openai-Thorp','https://raw.githubusercontent.com/openai/math/4eaee87548250b2682affda7d05d947c05554bae/preprints/Optimal-order-mixing-of-the-Thorp-shuffle-September-26-2026/build/main.tex')]
h=json.loads((P/'omega-head.body').read_text())['sha']
for n,path in [('omega-pop-md','Blueprint/D5/S3/Combinatorics/PopStack/PopStackParallel.md'),('omega-pop-lean','D5/S3/Combinatorics/PopStack/PopStackParallel.lean')]:jobs.append((n,'https://raw.githubusercontent.com/the-omega-institute/trureturing/'+h+'/'+path))
for job in jobs:print(get(job)[1])
