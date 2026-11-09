import pathlib,json,subprocess,hashlib
D=pathlib.Path(__file__).resolve().parents[1]
for p in (D/'sources').glob('*.pdf'):
 if p.read_bytes().startswith(b'%PDF'):subprocess.run(['pdftotext','-layout',str(p),str(p.with_suffix('.txt'))],check=True)
# retain compact actual historical matches excluding accidental numeric substrings
lines=(D/'history-matches.txt').read_text().splitlines(); ids=json.loads((D/'reservation.json').read_text())['ids']
import re
keep=[l for l in lines if len(l)<5000 and any(re.search(r'(?<![\da-f])'+str(i)+r'(?![\da-f])',l) for i in ids)]
(D/'outputs/history-filtered.txt').write_text('\n'.join(keep)+'\n')
for f in [D.parent/'ledger.json',D.parent.parent/'ledger.json',D.parent.parent/'prior-campaign-context.json']:
 j=json.loads(f.read_text()); print(str(f),hashlib.sha256(f.read_bytes()).hexdigest(),list(j)[:15]);print('reserved exact mentions',[(i,str(j).count(str(i))) for i in ids if str(i) in str(j)])
for p in (D/'sources').glob('*-head.json'):print(p.name,json.loads(p.read_text()).get('sha'))
