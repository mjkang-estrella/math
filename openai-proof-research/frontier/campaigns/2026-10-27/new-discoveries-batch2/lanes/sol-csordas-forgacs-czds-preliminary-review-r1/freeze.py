from pathlib import Path
import hashlib,json,shutil
L=Path(__file__).resolve().parent
B=L.parent.parent
S=L.parent/'sol-primary-analytic-arithmetic-scout-r287'
T=L.parent/'root-csordas-forgacs-triage-r1'
def h(p):return hashlib.sha256(p.read_bytes()).hexdigest()
rows=[]
files=[S/'PROOF.md',S/'moment-witness.json',T/'1505.00355v2.txt',T/'craven1995-correct.txt']
files+=list((S/'primary').glob('*'))
for i,p in enumerate(files):
 if not p.is_file():continue
 q=L/'frozen'/f'{i:02d}-{p.name}';q.parent.mkdir(exist_ok=True)
 a=h(p);shutil.copyfile(p,q);assert a==h(p)==h(q)
 rows.append(dict(original=str(p),copy=str(q.relative_to(L)),sha256=a,kind='scientific'))
for p in [B/'ledger.json',B/'prior-campaign-context.json',T/'STATUS.md',S/'provenance.json',S/'access.jsonl',S/'failures.md',Path('/home/mj-kang/Documents/Dev/math/openai-proof-research/AGENTS.md'),B/'AGENTS.md']:
 q=L/'administrative'/p.parent.name/p.name;q.parent.mkdir(parents=True,exist_ok=True);shutil.copyfile(p,q)
 rows.append(dict(original=str(p),copy=str(q.relative_to(L)),sha256=h(q),kind='administrative snapshot'))
(L/'bindings.json').write_text(json.dumps(rows,indent=2)+'\n')
print(json.dumps({'frozen':len(rows),'scientific':sum(r['kind']=='scientific' for r in rows)}))
