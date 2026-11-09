import pathlib,json,re,hashlib
L=pathlib.Path(__file__).resolve().parent;B=L.parent
pat=re.compile(r'328314|328558|328749|328770|328856|Golomb|Haarmann|Staecker|Fergusonian|Fox.*Nim|matching.derangement|capital.colou?r|concentric.cylinder|Davis.*stochastic|n.free|4.chordal|Bordeaux|330250|331498|331097|queen|polynomial.positivity',re.I)
out={}
D=B/'expanded-corpus-r253/http'
for p in D.iterdir():
 if not re.search(r'openai|omega|pool|projects',p.name) or p.name.endswith('.receipt.json') or p.stat().st_size>18000000:continue
 b=p.read_bytes();s=b.decode(errors='replace');matches=[];tr=None
 if p.suffix=='.json':
  try:
   d=json.loads(s)
   if isinstance(d,dict) and 'tree' in d:matches=[x['path'] for x in d['tree'] if pat.search(x['path'])];tr=d.get('truncated')
   else:matches=[t[:1500] for t in s.splitlines() if pat.search(t)]
  except:continue
 else:matches=[t[:1500] for t in s.splitlines() if pat.search(t)]
 out[str(p)]={'sha256':hashlib.sha256(b).hexdigest(),'truncated':tr,'matches':matches}
(L/'cached-registry-screen.json').write_text(json.dumps(out,indent=2))
print('cache files',len(out))
for p,d in out.items():
 if d['matches']:print(pathlib.Path(p).name, '\n'+'\n'.join(d['matches'][:20]))
hist=json.loads((L/'history-excerpts.json').read_text())
for d in hist:
 m=[t for i,t in d['matches'] if pat.search(t)]
 if m:print('HISTORY',pathlib.Path(d['path']).parent.name, '\n'+'\n'.join(m[:3]))
