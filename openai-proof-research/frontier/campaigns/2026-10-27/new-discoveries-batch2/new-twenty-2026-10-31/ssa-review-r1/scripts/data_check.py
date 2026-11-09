import pathlib,json,re,itertools
D=pathlib.Path(__file__).resolve().parents[1];j=json.loads((D.parent/'expanded-corpus-r104/outputs/ssa5-certificate.json').read_text());s=(D/'source-only/SSA5/Data.lean').read_text();W=[''.join(t) for t in itertools.product('ACGT',repeat=5)];r={}
for name,key in [('sTree','S'),('vTree','v'),('uTree','u')]:
 line=next(l for l in s.splitlines() if l.startswith('def '+name+' :')); vals=re.findall(r'\.leaf (true|false|\d+)',line);assert len(vals)==1024
 for w,v in zip(W,vals):
  if name=='sTree':assert (v=='true')==(w in j['S'])
  else:
   if w in j[key]:assert int(v)==j[key][w]
 r[name]='all 1024 entries match (vector entries outside domain masked in Lean)'
(D/'data-check.json').write_text(json.dumps(r,indent=2));print(r)
