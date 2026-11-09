exec(compile((__import__('pathlib').Path(__file__).parent/'research.py').read_text(),'research.py','exec'))
if sys.argv[1]=='history':
 prov=json.loads((P/'provenance.json').read_bytes())
 for i in r['ids']: print(i,prov[str(i)]['record']['statement'])
 matches=[]; inv=[]
 for name in json.loads((P/'historical-results-allowlist.json').read_bytes()):
  if any(x in name.lower() for x in ['crown','crown-coordinate-kernel-formal-pi-r14','transitive-bunkbed-state-bounds-formal-pi-r8']): continue
  p=pathlib.Path(name)
  try: data=p.read_bytes(); obj=json.loads(data)
  except Exception as e: inv.append(dict(path=name,error=str(e))); continue
  inv.append(dict(path=name,sha256=sha(data),bytes=len(data),depth='ID/title/source family scoped match of completed results'))
  text=data.decode()
  keys=[str(i) for i in ids]+['2007.13266','1909.06593','1802.04921','1804.10359','1909.10623','2011.02685','2012.03629','1902.05199']
  hits=[k for k in keys if k in text]
  if hits: matches.append(dict(path=name,hits=hits,record=obj))
 js('history-inventory.json',inv); js('history-matches.json',matches)
 for m in matches: print('HISTORY',m['path'],m['hits'],json.dumps(m['record'])[:16000])
 for name in ['ledger.json','STATUS.md']:
  p=P.parent/name
  if p.exists():
   data=p.read_text()
   if name.endswith('json'):
    o=json.loads(data); print('SCALARS', {k:v for k,v in o.items() if isinstance(v,(int,float,str)) and any(w in k.lower() for w in ['count','accepted','target'])})
   else: print('STATUS-SCALARS',[s for s in data.splitlines() if '52/60' in s or '52 / 60' in s][:3])
