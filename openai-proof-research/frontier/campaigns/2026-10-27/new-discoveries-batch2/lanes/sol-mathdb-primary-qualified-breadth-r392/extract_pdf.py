import pathlib,subprocess,json,hashlib
L=pathlib.Path(__file__).parent
for e in json.loads((L/'successor-provenance.json').read_text()):
 if 'file' not in e:continue
 p=L/e['file'];b=p.read_bytes();assert hashlib.sha256(b).hexdigest()==e['sha256'] and len(b)==e['size']
 subprocess.run(['pdftotext','-layout',str(p),str(p.with_suffix('.txt'))],check=True)
