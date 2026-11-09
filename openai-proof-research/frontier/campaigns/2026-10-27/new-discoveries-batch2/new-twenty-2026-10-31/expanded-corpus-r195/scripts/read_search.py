from pathlib import Path
import re,html
D=Path(__file__).resolve().parents[1]
for p in (D/'sources').glob('*literature.body'):
 s=p.read_text();s=re.sub(r'<(script|style)\b[^>]*>.*?</\1>','',s,flags=re.S);s=html.unescape(re.sub('<[^>]+>',' ',s));s=re.sub(r'\s+',' ',s)
 print(p.name, s[:650])
 (D/'outputs'/p.with_suffix('.txt').name).write_text(s)
