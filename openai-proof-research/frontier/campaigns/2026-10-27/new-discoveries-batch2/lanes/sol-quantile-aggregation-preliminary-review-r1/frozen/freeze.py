from pathlib import Path
import hashlib,json,shutil
B=Path('/home/mj-kang/Documents/Dev/math/openai-proof-research/frontier/campaigns/2026-10-27/new-discoveries-batch2')
L=Path(__file__).parent
S=B/'lanes/sol-fresh-analytic-wide-scout-r219'
records=[]
for src in [S/'SCOUTING.md',S/'sources/2007.12338.pdf',S/'work/2007.12338.txt',S/'freeze.json',S/'provenance.json']:
 if not src.exists(): continue
 before=hashlib.sha256(src.read_bytes()).hexdigest()
 dst=L/'frozen'/src.name;dst.parent.mkdir(exist_ok=True);shutil.copyfile(src,dst)
 assert before==hashlib.sha256(src.read_bytes()).hexdigest()==hashlib.sha256(dst.read_bytes()).hexdigest()
 dst.chmod(0o444)
 records.append(dict(original=str(src),copy=str(dst.relative_to(L)),sha256=before))
for name in ['AGENTS.md','ledger.json','prior-campaign-context.json']:
 dst=L/'administrative'/name;dst.parent.mkdir(exist_ok=True);shutil.copyfile(B/name,dst)
(L/'freeze.json').write_text(json.dumps(records,indent=2))
print(json.dumps(records,indent=2))
