import pathlib,json,hashlib,subprocess
D=pathlib.Path(__file__).resolve().parents[1];B=D.parent.parent
out={}
for p in [B/'ledger.json',B/'prior-campaign-context.json',D.parent/'ledger.json']:
 b=p.read_bytes();o=json.loads(b);out[str(p)]={'sha256':hashlib.sha256(b).hexdigest(),'keys':list(o),'accepted':o.get('accepted',[]),'excluded_after_review':o.get('excluded_after_review',{})}
(D/'outputs/context.json').write_text(json.dumps(out,indent=2))
for p in (D/'sources').glob('*.pdf'):
 subprocess.run(['pdftotext','-layout',str(p),str(p.with_suffix('.txt'))],check=True)
for p in (D/'sources').glob('*.txt'):
 lines=p.read_text().splitlines();hits=[]
 for i,l in enumerate(lines):
  if any(w in l.lower() for w in ['conjectur','observation 1','verified','checked','experiment']):hits.append('\n'.join(lines[max(0,i-2):i+9]))
 (D/'outputs'/f'{p.stem}-extract.txt').write_text('\n\n'.join(hits))
print('context read and primary PDF text extracted')
