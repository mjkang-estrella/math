from pathlib import Path
exec((Path(__file__).parent/'fetch_sources.py').read_text().split('jobs=[]')[0])
jobs=[('matroid-public-prior.html','https://probxiv.com/problems/topological-representations-of-matroid-maps'),('owr.pdf','https://content.ems.press/assets/public/full-texts/serials/owr/2/1/784/online/10.4171-owr-2005-03.pdf'),('registry-projects.yml','https://raw.githubusercontent.com/Vilin97/lean-pool/HEAD/LeanPool/projects.yml'),('registry-LeanPool.lean','https://raw.githubusercontent.com/Vilin97/lean-pool/HEAD/LeanPool.lean'),('stern-companion.pdf','https://arxiv.org/pdf/1102.5109'),('stern-2025.pdf','https://arxiv.org/pdf/2511.03847')]
with concurrent.futures.ThreadPoolExecutor(max_workers=2) as pool:
 for a in pool.map(fetch,jobs):receipts.append(a);print(a['file'].split('/')[-1],a.get('status',a.get('error')),flush=True)
(p/'final-receipts.json').write_text(json.dumps(receipts,indent=2)+'\n')
