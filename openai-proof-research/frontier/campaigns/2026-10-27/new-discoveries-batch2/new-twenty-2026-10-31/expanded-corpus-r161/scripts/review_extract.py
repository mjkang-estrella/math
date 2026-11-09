import pathlib,json,re,hashlib
D=pathlib.Path(__file__).resolve().parents[1]; B=D.parent.parent
for p in [B/'ledger.json',B/'prior-campaign-context.json',D.parent/'ledger.json']:
 o=json.loads(p.read_text());print('LEDGER',p,'SHA',hashlib.sha256(p.read_bytes()).hexdigest())
 def walk(x):
  if isinstance(x,dict):
   if ('title' in x or 'mathdb_id' in x) and any(k in x for k in ['status','outcome']):print({k:v for k,v in x.items() if k in ['title','mathdb_id','status','outcome','reason']})
   for v in x.values():walk(v)
  elif isinstance(x,list):
   for v in x:walk(v)
 walk(o)
for r in json.loads((D/'reservation.json').read_text())['rows']:
 a=r['source_url'].split('/')[-1];p=D/'sources'/f'{a}.txt';lines=p.read_text().splitlines()
 print('\nTARGET',r['mathdb_id'],r['title'])
 for i,l in enumerate(lines):
  if re.search(r'Conjecture|conjecture|disprov|counterexample|now proved',l):
   print('\n'.join(f'{j+1}: {lines[j]}' for j in range(max(0,i-2),min(len(lines),i+10))))
