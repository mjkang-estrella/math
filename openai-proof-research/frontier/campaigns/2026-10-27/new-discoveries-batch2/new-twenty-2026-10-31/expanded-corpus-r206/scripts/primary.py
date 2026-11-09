import sys,pathlib,json,re
sys.path.insert(0,str(pathlib.Path(__file__).resolve().parent));from net import get,D
if sys.argv[1]=='extra':
 todo=[('ghost-bounds.pdf','https://arxiv.org/pdf/1502.05727'),('saxl-counterexample.pdf','https://arxiv.org/pdf/2609.01367'),('ionization-report.pdf','https://ems.press/content/serial-article-files/46403'),('meander-journal.pdf','https://uwaterloo.ca/math/sites/default/files/uploads/documents/goulnicapruder2017_170805188.pdf'),('trees-journal.pdf','https://www.combinatorics.org/ojs/index.php/eljc/article/download/v23i4p42/pdf/'),('turan-journal.pdf','https://rucinski.home.amu.edu.pl/papers/ejaT.pdf')]
 for k,u in todo:get(k,u)
if sys.argv[1]=='metadata':
 for p in sorted((D/'sources').glob('*-abs.html')):
  if not re.match(r'\d{4}\.\d',p.name):continue
  s=p.read_text();print(p.name)
  for pat in [r'<td class="tablecell jref">(.*?)</td>',r'<td class="tablecell doi">(.*?)</td>']:
   print(re.sub('<[^>]*>',' ',''.join(re.findall(pat,s,re.S))))
if sys.argv[1]=='paths':
 ids=list(json.loads((D/'extracted.json').read_text()))
 for p in (D/'sources').glob('*-complete.json'):
  t=json.loads(p.read_text());print(p.name,'truncated',t.get('truncated'),'entries',len(t['tree']))
  hits=[o['path'] for o in t['tree'] if any(re.search(r'(?<!\d)'+i+r'(?!\d)',o['path']) for i in ids) or re.search('meandr|heterochrom|ghost.?number|excessive|Saxl|saxl|fighting.?fish|cross.?number|nested.?cartesian|ban.?linial|clique.?width',o['path'],re.I)]
  (D/f'outputs/{p.stem}-hits.json').write_text(json.dumps(hits,indent=2));print('\n'.join(hits))
