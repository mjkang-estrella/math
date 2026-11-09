from pathlib import Path
import re,html
L=Path(__file__).parent
for p in (L/'primary').glob('*.html'):
 t=html.unescape(re.sub('<[^>]+>',' ',p.read_text()))
 p.with_suffix('.txt').write_text(t)
 print(p.name, re.sub(r'\s+',' ',t)[-19000:])
