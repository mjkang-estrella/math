from pathlib import Path
import hashlib,subprocess
r=Path(__file__).resolve().parent
f=r/'extend-r8.py';t=f.read_text().replace('import json,re,hashlib,zipfile,shutil','import json,re,hashlib,zipfile,shutil,textwrap').replace("original=(p/'module-order.txt').read_text().splitlines()","original=zipfile.ZipFile(r/'r7-source.zip').read('module-order.txt').decode().splitlines()").replace('old[int(m[1])]=m[2].strip()','old[int(m[1])]=textwrap.dedent(m[2]).strip()')
f.write_text(t)
