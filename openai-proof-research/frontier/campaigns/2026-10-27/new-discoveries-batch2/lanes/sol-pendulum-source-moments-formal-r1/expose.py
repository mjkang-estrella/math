from pathlib import Path
r=Path(__file__).resolve().parent/'formal'
for p in r.glob('*.lean'):
 s=p.read_text().replace('public import all ','public import ')
 s=s.replace('\ndef ','\n@[expose] def ')
 p.write_text(s)
