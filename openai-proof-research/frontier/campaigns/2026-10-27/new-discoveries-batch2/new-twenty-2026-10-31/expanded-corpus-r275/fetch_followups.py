from pathlib import Path
exec((Path(__file__).parent/'fetch_sources.py').read_text().split('jobs=[]')[0])
jobs=[('chen-tseng.pdf','https://arxiv.org/pdf/1208.0851v2'),('pulaj.pdf','https://arxiv.org/pdf/1903.02317v1'),('cukic-kozlov.pdf','https://arxiv.org/pdf/math/0410335'),('bekmetjev.pdf','https://arxiv.org/pdf/math/0406068'),('mohar-snarks.pdf','https://users.fmf.uni-lj.si/mohar/Reprints/2008/BM08_AMC1_Steffen_Snarks.pdf'),('drake-citing.html','https://cs.uwaterloo.ca/journals/JIS/VOL13/Drake/drake6.html')]
with concurrent.futures.ThreadPoolExecutor(max_workers=2) as pool:
 for a in pool.map(fetch,jobs):receipts.append(a);print(a['file'].split('/')[-1],a.get('status',a.get('error')),flush=True)
(p/'followup-receipts.json').write_text(json.dumps(receipts,indent=2)+'\n')
