from pathlib import Path
import re,html,json
D=Path(__file__).resolve().parents[1]
for p in (D/'sources').glob('[0-9]*.html'):
 t=p.read_text();t=re.sub(r'<math\b[^>]*alttext="([^"]*)"[^>]*>.*?</math>',lambda m:' '+html.unescape(m[1])+' ',t,flags=re.S)
 t=html.unescape(re.sub('<[^>]+>',' ',t));t=re.sub(r'\s+',' ',t)
 (D/'sources'/p.with_suffix('.txt').name).write_text(t)
for n in ['openai','omega']:
 d=json.load(open(D/f'sources/{n}-head.json')); print(n,d['sha'],d['commit']['committer']['date'])
