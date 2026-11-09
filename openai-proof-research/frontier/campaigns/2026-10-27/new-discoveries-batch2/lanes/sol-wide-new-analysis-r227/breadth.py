from retrieve import *
terms=['Markovian arrival','MMPP','MSPP','Hermite-Hadamard','Olivier','geodesic net','polling','wavelet','tiling by translates','Brownian sheet','Foss','OPSFA','Muckenhoupt']
refs=[];hits=[]
for p in L.parent.glob('*/SCOUTING.md'):
 if p.parent==L:continue
 h=hashlib.sha256(p.read_bytes()).hexdigest();refs.append({'path':str(p),'sha256':h})
(L/'history-freeze.json').write_text(json.dumps(refs,indent=2))
for r in refs:
 p=pathlib.Path(r['path']);s=p.read_text(errors='replace');assert hashlib.sha256(p.read_bytes()).hexdigest()==r['sha256']
 for t in terms:
  for line in s.splitlines():
   if t.lower() in line.lower():hits.append({'path':str(p),'term':t,'line':line[:1600]})
(L/'history-screen.json').write_text(json.dumps(hits,indent=2));print('HISTORY',json.dumps(hits))
ids=['1905.01736v1','1611.01905v1','1201.5156v1','1904.00483v1','1408.0142v1','1905.08230v1','2009.09410v2','math/0510518v1','0909.0462v1','1607.06196v2']
for id in ids:
 name=id.replace('/','_')+'.pdf';fetch('https://arxiv.org/pdf/'+id,name)
 print('FROZEN',id)
