import pathlib,sys,json
sys.path.insert(0,str(pathlib.Path(__file__).resolve().parent))
from fetch import fetch,D
sha=json.loads(next((D/'sources').glob('su-head-*/body')).read_text())['sha']
for path in ['README.md','Main.lean']:
 z=fetch(f'https://raw.githubusercontent.com/mysticflounder/schur-degree-block-sums/{sha}/{path}','su-'+path.replace('.','-'));print(path,z['status'])
