from pathlib import Path
import importlib.util
L=Path(__file__).resolve().parents[1];s=importlib.util.spec_from_file_location('fetch',L/'scripts/fetch.py');m=importlib.util.module_from_spec(s);s.loader.exec_module(m)
for a in ['1904.12727','2104.04330']:
 b=m.fetch('https://arxiv.org/pdf/'+a,a+'-extra')
 if b:(L/'sources'/f'{a}.pdf').write_bytes(b)
