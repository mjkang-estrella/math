import pathlib,json,hashlib,time
L=pathlib.Path(__file__).resolve().parent
def h(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def word(u,v,n):return (u+v*((n//len(v))+2))[:n]
def cover(u,v,q):
 # Independent occurrence-interval check, not the generating automaton.
 m=len(q);d=len(v);t=len(u)+m+d;n=t+d+2*m
 w=word(u,v,n);covered=[False]*(t+d)
 for i in range(n-m+1):
  if w[i:i+m]==q:
   for j in range(i,min(i+m,t+d)):covered[j]=True
 phases=[i for i in range(d) if word('',v,i+m)[i:i+m]==q]
 if not phases:return False
 gaps=[phases[i+1]-phases[i] for i in range(len(phases)-1)]+[phases[0]+d-phases[-1]]
 return all(covered) and max(gaps)<=m
manifest=json.loads((L/'finalmanifest.json').read_text());paths=[]
for r in manifest:
 p=L/r['path'];assert p.stat().st_size==r['bytes'];assert h(p)==r['sha256'];paths.append(r['path'])
assert 'finalmanifest.json' not in paths and 'verification-receipt.json' not in paths
assert set(paths)=={str(p.relative_to(L)) for p in L.rglob('*') if p.is_file() and p.name not in ['finalmanifest.json','verification-receipt.json']}
for r in json.loads((L/'frozenbindings.json').read_text()):
 assert h(pathlib.Path(r['original']))==h(pathlib.Path(r['copy']))==r['sha256']
data=json.loads((L/'lasso-checks.json').read_text());assert len(data['witnesses'])==data['certified']==92
for r in data['witnesses']:
 u,v=r['u'],r['v'];n=len(u)+len(v);p=word(u,v,n)
 assert all(p!=word('',v,n+len(v))[j:j+n] for j in range(len(v)))
 assert not any(cover(u,v,p[:m]) for m in range(1,n))
 f={'a':r['a'],'b':r['b']};assert cover(''.join(f[c] for c in u),''.join(f[c] for c in v),r['q'])
assert cover('ab','aba','aba')
assert cover('abbab','abb','abbab')
assert not cover('a','b','ab')
receipt={'status':'PASS','manifest_sha256':h(L/'finalmanifest.json'),'entries':len(paths),'inherited_original_copy_checks':len(json.loads((L/'frozenbindings.json').read_text())),'independently_verified_lasso_certificates':92,'return_code_obstruction':True,'full_source_conjecture_proved':False,'discovery_credit':0,'utc':time.strftime('%Y-%m-%dT%H:%M:%SZ',time.gmtime())}
(L/'verification-receipt.json').write_text(json.dumps(receipt,indent=2));print(json.dumps(receipt))
