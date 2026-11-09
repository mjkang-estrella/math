from pathlib import Path
import json
D=Path(__file__).resolve().parents[1];x={'__file__':str(D/'scripts/exact.py')};exec((D/'scripts/exact.py').read_text().split('witness=list(')[0],x)
es=[(0,1),(0,2),(0,3),(1,2),(1,3),(2,3),(0,4)]
r={a:x['calc'](5,es,a,True) for a in [-1,0,1]}
(D/'outputs/minimal-MP-certificate.json').write_text(json.dumps(x['serial'](r),indent=2))
