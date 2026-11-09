import sys,pathlib,json,subprocess,re,importlib.util
sys.path.insert(0,str(pathlib.Path(__file__).resolve().parent))
from fetch import fetch,D
out=json.loads((D/'outputs/registry-screen.json').read_text());sha=out['heads']['the-omega-institute/trureturing']
urls=[f'https://raw.githubusercontent.com/the-omega-institute/trureturing/{sha}/D5/S3/StatisticalMechanics/HardCore/HardSquareNecklacePeriod.lean','https://www.trureturing.org/research/cioni-ferrari-smith-pop-stack-simple/','https://www.cambridge.org/core/services/aop-cambridge-core/content/view/786F8F012E6153C711868DE147A493C0/S2050509421000475a.pdf/symmetry-of-narayana-numbers-and-rowvacuation-of-root-posets.pdf','https://www.numdam.org/item/ALCO_2022__5_6_1205_0.pdf','https://doi.org/10.1112/plms.70026','https://www.nathanmcnew.com/Convex.pdf']
for n,u in enumerate(urls):
 r=fetch(u,'primary-'+str(n));out['receipts'].append(r)
 if r.get('status')==200 and pathlib.Path(r['body']).read_bytes().startswith(b'%PDF'):subprocess.run(['pdftotext','-layout',r['body'],str(D/f'outputs/primary-{n}.txt')])
(D/'outputs/registry-screen.json').write_text(json.dumps(out,indent=2))
for m in ['networkx','pynauty','sympy','scipy']: print(m,importlib.util.find_spec(m) is not None)
# Compact matches rather than serialized multi-megabyte lines.
for r in out['receipts']:
 if r.get('status')==200 and 'git/trees/' in r['url']:
  t=json.loads(pathlib.Path(r['body']).read_text());print(r['url'],'truncated',t.get('truncated'))
  for x in t.get('tree',[]):
   if re.search('boone|panyushev|hard.?square|symplectic.content|quadrangulation|bruhat.*automorph',x['path'],re.I):print(x['path'])
