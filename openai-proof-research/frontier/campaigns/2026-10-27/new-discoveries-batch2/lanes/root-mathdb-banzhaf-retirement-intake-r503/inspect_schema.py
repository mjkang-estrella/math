import pathlib,json
P=pathlib.Path(__file__).resolve().parent
for p in sorted((P/'frozen').rglob('*.json')):
 if p.name not in {'manifest.json','bindings.json','coverage-delta.json','hypothesis-queue.json','adjudications.json','reserved-ids.json','dispositions.json','final-receipt.json'}: continue
 o=json.loads(p.read_text()); print(str(p.relative_to(P)))
 if isinstance(o,list): print('LIST',len(o),json.dumps(o[:1])[:1800])
 else: print('KEYS',list(o)[:25],json.dumps(o if len(json.dumps(o))<2200 else {k:(v[:1] if isinstance(v,list) else list(v)[:3] if isinstance(v,dict) else v) for k,v in list(o.items())[:10]})[:2200])
