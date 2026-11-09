from pathlib import Path
import json,hashlib,re,subprocess
L=Path(__file__).resolve().parent
for p in (L/'http').glob('*.pdf'):
 if p.read_bytes()[:4]==b'%PDF':subprocess.run(['pdftotext','-layout',str(p),str(p.with_suffix('.txt'))],timeout=15,check=False)
ids=json.loads((L/'reservation.json').read_text())['ids'];pat=re.compile('|'.join(map(str,ids))+r'|Pascal rhombus|J170|two.tailed.comet|minimal.dendrimer|Clifford basis|binary.word.maximal|rectangular Narayana|sphere.function',re.I)
h=[]
for base in [L.parent,L.parent.parent/'lanes']:
 for p in base.glob('*/*'):
  if not p.is_file() or p.parent==L or p.suffix not in ['.md','.json','.txt'] or not any(z in p.name.lower() for z in ['result','summary','review','reject','hold','ledger','notes']):continue
  if p.stat().st_size>2000000:continue
  try:s=p.read_text()
  except:continue
  if pat.search(s):h.append({'path':str(p),'sha256':hashlib.sha256(p.read_bytes()).hexdigest(),'lines':[{'n':n,'text':t} for n,t in enumerate(s.splitlines(),1) if pat.search(t)]})
(L/'history.json').write_text(json.dumps(h,indent=2));print('history files',len(h))
for x in h:print(x['path'],str(x['lines'])[:1600])
for p in [L.parent/'ledger.json',L.parent.parent/'ledger.json',L.parent/'STATUS.md',L.parent/'root-intake-r60/reserve8.py']:
 s=p.read_text();(L/(p.parent.name+'-'+p.name+'.receipt.json')).write_text(json.dumps({'path':str(p),'sha256':hashlib.sha256(p.read_bytes()).hexdigest(),'keys':list(json.loads(s)) if p.suffix=='.json' else None}));print('context',p,len(s))
