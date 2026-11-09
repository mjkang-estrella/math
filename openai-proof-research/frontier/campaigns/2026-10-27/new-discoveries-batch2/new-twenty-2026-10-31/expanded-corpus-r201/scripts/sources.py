import sys,pathlib,json,time
sys.path.insert(0,str(pathlib.Path(__file__).resolve().parent))
from fetch import fetch,D
rows=json.loads((D/'extracted.json').read_text());out=[]
for aid in dict.fromkeys(o['source_url'].rsplit('/',1)[-1] for o in rows.values()):
 r=fetch('https://arxiv.org/abs/'+aid,'arxiv-'+aid);out.append(r)
 print(aid,r['status'],flush=True)
(D/'outputs/source-receipts.json').write_text(json.dumps(out,indent=2))
