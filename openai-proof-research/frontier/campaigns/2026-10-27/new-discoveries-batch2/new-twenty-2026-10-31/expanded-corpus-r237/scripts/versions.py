from pathlib import Path
import re,runpy,json
L=Path(__file__).resolve().parents[1];get=runpy.run_path(str(L/'scripts/http.py'))['get']
for p in (L/'sources').glob('*.abs.html'):
 vs=list(map(int,re.findall(r'\[v(\d+)\]',p.read_text())))
 a=p.name.split('.abs.')[0]
 for v in sorted(set(vs)):
  if v==max(vs):continue
  get(f'{a}v{v}.pdf',f'https://arxiv.org/pdf/{a}v{v}')
sha=json.loads((L/'sources/lean-pool-head.json').read_text())['sha']
get('pool-projects.yml',f'https://raw.githubusercontent.com/Vilin97/lean-pool/{sha}/.github/projects.yml')
for key,url in [('carbonero-journal.pdf','https://ajc.maths.uq.edu.au/pdf/83/ajc_v83_p348.pdf'),('eventown-2026.pdf','https://arxiv.org/pdf/2608.16321'),('derangement-complete.pdf','https://arxiv.org/pdf/2010.06431'),('q-decompositions.pdf','https://pure.tue.nl/ws/portalfiles/portal/352943533/23m156358x.pdf')]:get(key,url)
