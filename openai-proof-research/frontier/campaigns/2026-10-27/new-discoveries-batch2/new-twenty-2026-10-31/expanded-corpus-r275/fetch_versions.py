from pathlib import Path
exec((Path(__file__).parent/'fetch_sources.py').read_text().split('jobs=[]')[0])
import re
jobs=[]
for row in r['rows']:
 i=row['mathdb_id'];f=s/f'{i}-abs.html'
 if not f.exists():continue
 versions=sorted(set(re.findall(r'\[v(\d+)\]',f.read_text())))
 for v in versions:jobs.append((f'{i}-v{v}.pdf',row['source_url'].replace('/abs/','/pdf/')+'v'+v))
jobs += [('drake-journal.pdf','https://cs.uwaterloo.ca/journals/JIS/VOL13/Drake/dyck-schroeder.pdf'),('ghorpade-journal.pdf','https://www.math.iitb.ac.in/~srg/preprints/FFA_816_RevisedProofs.pdf'),('registry-conjectures.html','https://www.trureturing.org/conjectures'),('registry-openai-overview.tex','https://raw.githubusercontent.com/openai/math/main/overview.tex')]
with concurrent.futures.ThreadPoolExecutor(max_workers=2) as pool:
 for a in pool.map(fetch,jobs):receipts.append(a);print(a['file'].split('/')[-1],a.get('status',a.get('error')),flush=True)
(p/'version-receipts.json').write_text(json.dumps(receipts,indent=2)+'\n')
