import pathlib,json,re
D=pathlib.Path(__file__).resolve().parents[1]; todo=[]
for name,repo in [('openai','openai/math'),('leanpool','Vilin97/lean-pool'),('omega','the-omega-institute/trureturing')]:
 h=json.loads((D/f'sources/{name}-head.json').read_text())['sha'];todo.append((name+'-tree.json',f'https://api.github.com/repos/{repo}/git/trees/{h}?recursive=1'))
for p in (D/'sources').glob('*.abs'):
 vs=re.findall(r'\[v(\d+)\]',p.read_text()); top=max(map(int,vs))
 for v in range(1,top): todo.append((p.stem+f'v{v}.pdf',f'https://arxiv.org/pdf/{p.stem}v{v}'))
todo += [('star-colimits.pdf','https://uu.diva-portal.org/smash/get/diva2:1789881/FULLTEXT01.pdf'),('locating-2024.pdf','https://perso.limos.fr/ffoucaud/Publications/Papers/J52_L-NL-coloring-sparse_DAM_2024.pdf'),('crowns-2026.abs','https://arxiv.org/abs/2609.35842'),('crowns-2026.pdf','https://arxiv.org/pdf/2609.35842')]
(D/'queue2.json').write_text(json.dumps(todo))
