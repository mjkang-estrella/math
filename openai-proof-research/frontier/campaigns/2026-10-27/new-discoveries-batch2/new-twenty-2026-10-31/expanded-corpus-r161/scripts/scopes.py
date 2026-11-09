import json,pathlib,urllib.request,hashlib,datetime
D=pathlib.Path(__file__).resolve().parents[1];root=json.loads((D/'sources/omega-root.json').read_text());receipts=[]
for name in ['D5','Problems']:
 e=next(e for e in root['tree'] if e['path']==name);url=e['url']+'?recursive=1';r={'scope':name,'tree_sha':e['sha'],'url':url,'utc':datetime.datetime.now(datetime.timezone.utc).isoformat()}
 try:
  with urllib.request.urlopen(url,timeout=25) as f:b=f.read();r['status']=f.status
  (D/'sources'/f'omega-{name}-tree.json').write_bytes(b);o=json.loads(b);r.update(sha256=hashlib.sha256(b).hexdigest(),truncated=o.get('truncated'),paths=len(o['tree']))
  pats=['oddtown','spreading','divine','zeroLinear','deepzero','grunbaum','partialdual','betweenness','condorcet','partitionrank','analyticrank']+[str(x) for x in json.loads((D/'reservation.json').read_text())['ids']]
  r['matches']=[e['path'] for e in o['tree'] if any(q.lower() in e['path'].lower() for q in pats)]
 except Exception as ex:r['error']=str(ex)
 receipts.append(r);print(r,flush=True)
(D/'outputs/registry-scopes.json').write_text(json.dumps(receipts,indent=2)+'\n')
