import json,pathlib
D=pathlib.Path(__file__).resolve().parents[1]
t=[('yip-2610.01657.html','https://arxiv.org/html/2610.01657'),('six-spin.html','https://hexagonmath.org/2610.00241v1'),('forgotten.html','https://doi.org/10.46793/match.95-1.10924'),('BICA2024-43.pdf','https://bica.the-ica.org/Volumes/106/Reprints/BICA2024-43-Reprint.pdf')]
for owner,repo in [('Vilin97','lean-pool'),('openai','math'),('the-omega-institute','trureturing')]:
 sha=json.loads((D/'sources'/(owner+'-head.json')).read_text())['sha'];t.append((owner+'-README.md',f'https://raw.githubusercontent.com/{owner}/{repo}/{sha}/README.md'))
(D/'extras-plan.json').write_text(json.dumps(t))
