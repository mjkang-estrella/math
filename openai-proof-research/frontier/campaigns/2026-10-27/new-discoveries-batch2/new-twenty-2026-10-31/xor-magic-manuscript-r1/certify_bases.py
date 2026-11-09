from pathlib import Path
import re,json,functools,operator,hashlib
R=Path(__file__).resolve().parent; F=R/'dossier/formal'
data={}; receipt=[]
for p in sorted(F.glob('Base[13][62]*.lean')):
 s=p.read_text(); a=re.search(r'def masks.*?:= !\[([^\]]+)\]',s)
 if not a: continue
 masks=list(map(int,a[1].split(',')));N=len(masks);closed='Closed' in p.stem;d=int(re.search(r'(?:Open|Closed)(\d+)',p.stem)[1])
 parents=list(map(int,re.search(r'def parents.*?:= !\[([^\]]+)\]',s)[1].split(',')))
 ranks=list(map(int,re.search(r'def ranks.*?:= !\[([^\]]+)\]',s)[1].split(',')))
 for v,m in enumerate(masks):
  ns=[u for u in range(N) if (m>>u)&1]
  assert not (m>>v)&1 and len(ns)==d
  assert all((masks[u]>>v)&1 for u in ns)
  assert functools.reduce(operator.xor,ns,v if closed else 0)==0
  if v: assert parents[v] in ns and ranks[parents[v]]<ranks[v]
 data[p.stem]={'N':N,'d':d,'closed':closed,'masks_hex':[format(x,'x') for x in masks],'parents':parents,'ranks':ranks}
 receipt.append({'module':p.stem,'regular':True,'zero_xor':True,'symmetric_loopless':True,'direct_descent_connected':True})
(R/'dossier/base-data.json').write_text(json.dumps(data,indent=2)+'\n')
(R/'receipts/base-check.json').write_text(json.dumps({'status':'PASS','witnesses':receipt},indent=2)+'\n')
print(len(data),'direct base certificates PASS')
