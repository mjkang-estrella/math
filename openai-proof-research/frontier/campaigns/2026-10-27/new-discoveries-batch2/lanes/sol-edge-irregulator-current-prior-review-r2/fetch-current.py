import urllib.request,urllib.error,json,hashlib,datetime
from pathlib import Path
P=Path(__file__).resolve().parent;D=P/'live';D.mkdir(exist_ok=True)
urls={
'publisher-chapter':'https://link.springer.com/chapter/10.1007/978-981-95-7127-7_24',
'arxiv-current':'https://arxiv.org/abs/2511.14514',
'omega-order':'https://raw.githubusercontent.com/the-omega-institute/trureturing/70af54071bfd4ac098619a9db8c16bb6f7aced11/D5/S3/Combinatorics/ErdosGrahamOrderGadget.lean',
'omega-response':'https://raw.githubusercontent.com/the-omega-institute/trureturing/70af54071bfd4ac098619a9db8c16bb6f7aced11/D5/S3/ConceptDynamics/Coding/FirstResponseDiamond.lean',
'omega-harder':'https://raw.githubusercontent.com/the-omega-institute/trureturing/70af54071bfd4ac098619a9db8c16bb6f7aced11/Library/ConceptDynamics/harder2025linkirregular.md',
'omega-beluhov':'https://raw.githubusercontent.com/the-omega-institute/trureturing/70af54071bfd4ac098619a9db8c16bb6f7aced11/Library/Combinatorics/beluhov2026diamond.md',
'openai-neighbor':'https://raw.githubusercontent.com/openai/math/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Probability/BenjaminiSchramm/NeighborDegreeBound.lean',
'openai-378':'https://raw.githubusercontent.com/openai/math/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/docs/378.md'
}
rows=[]
for name,url in urls.items():
 row={'name':name,'url':url,'utc_start':datetime.datetime.now(datetime.timezone.utc).isoformat()}
 try:
  with urllib.request.urlopen(url,timeout=18) as r:data=r.read();row.update(status=r.status,final_url=r.url,headers=dict(r.headers))
 except urllib.error.HTTPError as e:
  data=e.read();row.update(status=e.code,final_url=e.url,error=str(e))
 except Exception as e:data=b'';row.update(error=repr(e))
 (D/name).write_bytes(data);row.update(sha256=hashlib.sha256(data).hexdigest(),bytes=len(data),utc_end=datetime.datetime.now(datetime.timezone.utc).isoformat());rows.append(row)
 (D/'http.json').write_text(json.dumps(rows,indent=2))
 print(name,row.get('status'),len(data),flush=True)
