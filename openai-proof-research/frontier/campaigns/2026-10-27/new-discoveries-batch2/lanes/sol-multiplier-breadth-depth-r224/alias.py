import pathlib,json,re,hashlib
L=pathlib.Path(__file__).resolve().parent
terms=['2609.28707','Alzer','Krasniqi','boundary.contact','2608.17927','Mendon','dense.sampling','stable autoregressive','2502.02989','fractal curvature','2608.02288','covariogram','2502.13819','singular value spectrum','2608.11686','fractional ground state','2609.23051','polygon.*torsion','2609.11418','Ball.Nayar.Tkocz']
hits=[];changed=[]
for row in json.loads((L/'history-bindings.json').read_text()):
 p=pathlib.Path(row['path'])
 h=hashlib.sha256(p.read_bytes()).hexdigest()
 if h!=row['sha256']:changed.append(str(p));continue
 s=p.read_text(errors='replace');matches=[]
 for t in terms:
  m=re.search(t,s,re.I)
  if m:matches.append({'term':t,'context':s[max(0,m.start()-160):m.end()+420]})
 if matches:hits.append({'path':str(p),'matches':matches})
 assert hashlib.sha256(p.read_bytes()).hexdigest()==h
(L/'alias-results.json').write_text(json.dumps({'terms':terms,'changed_administrative_or_active':changed,'hits':hits},indent=2))
for h in hits:
 if any(m['term'] in ['2609.28707','2608.17927','boundary.contact','stable autoregressive','dense.sampling'] for m in h['matches']):print(h)
print('hits',len(hits),'changed',len(changed))
