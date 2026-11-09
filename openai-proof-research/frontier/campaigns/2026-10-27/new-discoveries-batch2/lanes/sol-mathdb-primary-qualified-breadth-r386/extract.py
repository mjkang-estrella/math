import pathlib,json,hashlib,subprocess,re
L=pathlib.Path(__file__).resolve().parent
for p in (L/'primary').glob('*.body'):
 m=json.loads(p.with_suffix('.meta.json').read_text());b=p.read_bytes();assert hashlib.sha256(b).hexdigest()==m['sha256']
 if b.startswith(b'%PDF'):subprocess.run(['pdftotext','-layout',str(p),str(p.with_suffix('.txt'))],check=True)
 else:
  s=b.decode();print(p.name, '\n'.join(sorted(set(re.findall(r'https?[^\s"<>\\]+',s)))[:40]))
