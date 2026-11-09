from pathlib import Path
p=Path(__file__).resolve().parent
exec((p/'fetch.py').read_text().split('rows=json.loads')[0])
exec('def fetch(url):'+(p/'fetch.py').read_text().split('def fetch(url):')[1].split('with concurrent.futures')[0])
import subprocess
r=fetch('https://www.impan.pl/shop/en/publication/transaction/download/product/83466');(p/'hegarty-receipt.json').write_text(json.dumps(r,indent=2)+'\n')
f=p/r['file']
if f.exists() and f.read_bytes()[:4]==b'%PDF':
 t=f.with_suffix('.txt');subprocess.run(['pdftotext','-layout',str(f),str(t)],timeout=20);l=t.read_text().splitlines();idx=next(i for i,x in enumerate(l) if 'Theorem 8.' in x);print('\n'.join(f'{j+1}: {l[j]}' for j in range(max(0,idx-5),min(len(l),idx+150))))
print(json.dumps(r))
