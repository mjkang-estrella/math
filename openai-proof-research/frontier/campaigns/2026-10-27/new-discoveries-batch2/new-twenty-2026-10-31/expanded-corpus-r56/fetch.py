from pathlib import Path
import requests,hashlib,json,datetime,subprocess
w=Path(__file__).resolve().parent
jobs=[('openai-head','https://api.github.com/repos/OpenAI/math/commits/HEAD'),('omega-head','https://api.github.com/repos/leanprover-community/Proofs/commits/HEAD')]
# Omega URL taken from inherited receipt, not guessed.
r=json.loads((w.parent/'staller-parent-final-r1/registry-corrected-refresh.json').read_text());print(json.dumps(r)[:4000])
for k,u in jobs[:1]+[(a,'https://arxiv.org/pdf/'+a) for a in ['2402.00237','2402.06008','2403.06318','2402.09254','2402.18955','2402.17413']]:
 t=datetime.datetime.now(datetime.timezone.utc).isoformat()
 try:
  z=requests.get(u,timeout=25); b=z.content;(w/'sources'/f'{k}.bin').write_bytes(b);d={'utc':t,'url':u,'final_url':z.url,'status':z.status_code,'sha256':hashlib.sha256(b).hexdigest(),'bytes':len(b)}
  if z.status_code==200 and b.startswith(b'%PDF'):subprocess.run(['pdftotext','-layout',str(w/'sources'/f'{k}.bin'),str(w/'sources'/f'{k}.txt')],check=True)
 except Exception as e:d={'utc':t,'url':u,'error':str(e)}
 (w/'sources'/f'{k}.receipt.json').write_text(json.dumps(d,indent=2));print(d,flush=True)
