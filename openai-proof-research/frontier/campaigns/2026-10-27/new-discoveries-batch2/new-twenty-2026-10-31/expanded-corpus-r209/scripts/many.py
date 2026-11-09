import sys,importlib.util,time,json
from pathlib import Path
L=Path(sys.argv[1]).resolve()
s=importlib.util.spec_from_file_location('f',str(L/'scripts/fetch.py'));f=importlib.util.module_from_spec(s);s.loader.exec_module(f)
f.L=L
for line in Path(sys.argv[2]).read_text().split('\n'):
    if not line.strip(): continue
    label,url=line.split(None,1)
    f.fetch(url.strip(),label); time.sleep(float(sys.argv[3]) if len(sys.argv)>3 else 3)
