import pathlib,json,urllib.request,hashlib,datetime,subprocess
D=pathlib.Path(__file__).resolve().parents[1];out=[]
urls={'pool-projects':'https://raw.githubusercontent.com/Vilin97/lean-pool/01db1d7049cf9668bda1e9e106875ee1278b43e6/LeanPool/projects.yml','omega-head':'https://api.github.com/repos/the-omega-institute/trureturing/commits/HEAD','openai-head':'https://api.github.com/repos/openai/math/commits/HEAD','secure':'https://arxiv.org/pdf/2103.01406','takaoka':'https://arxiv.org/pdf/2211.04871','hypergraph2026':'https://arxiv.org/pdf/2609.17468','ballot':'https://arxiv.org/pdf/2103.04599'}
for name,u in urls.items():
 r={'url':u,'utc':datetime.datetime.now(datetime.timezone.utc).isoformat()};p=D/'sources/extra'/name;p.mkdir(parents=True,exist_ok=True)
 try:
  with urllib.request.urlopen(u,timeout=18) as f:b=f.read();r.update(status=f.status,sha256=hashlib.sha256(b).hexdigest());(p/'raw').write_bytes(b)
  if b.startswith(b'%PDF'):subprocess.run(['pdftotext','-layout',str(p/'raw'),str(p/'text.txt')])
 except Exception as e:r['error']=str(e)
 out.append(r);(D/'outputs/extra-receipts.json').write_text(json.dumps(out,indent=2));print(name,r,flush=True)
