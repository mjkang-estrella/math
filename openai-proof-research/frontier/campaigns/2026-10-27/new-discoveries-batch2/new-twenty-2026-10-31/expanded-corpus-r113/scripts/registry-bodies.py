import pathlib,json
from fetch import get
D=pathlib.Path(__file__).resolve().parents[1];h=json.loads((D/'sources/omega-head.json').read_text())['sha']
for path in ['D5/S3/Combinatorics/CylindricPartition/LiUncu.lean','D5/S3/Combinatorics/CylindricPartition/LiUncuDefs.lean','D5/S3/Combinatorics/CylindricPartition/LiUncuPaths.lean','D5/S3/Combinatorics/CylindricPartition/LiUncuPathSums.lean']:
 print(get((path.rsplit('/',1)[-1],f'https://raw.githubusercontent.com/the-omega-institute/trureturing/{h}/{path}')),flush=True)
