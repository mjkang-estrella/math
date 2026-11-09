from pathlib import Path
import json,hashlib
L=Path(__file__).parent
for name in ['ledger.json','prior-campaign-context.json']:
 d=json.loads((L/'administrative'/name).read_text())
 print(name,'keys',list(d),'counts',{k:d[k] for k in ['accepted_count','total_accepted_count','next_global_outcome_number'] if k in d})
for name in ['convolution.txt','negative-dependence.txt','joint2016.txt']:
 (L/'sources'/name).chmod(0o444)
manifest={str(p.relative_to(L)):hashlib.sha256(p.read_bytes()).hexdigest() for p in sorted(L.rglob('*')) if p.is_file() and p.name not in ['manifest.json','verification-receipt.json']}
(L/'manifest.json').write_text(json.dumps(manifest,indent=2));print('manifest entries',len(manifest))
