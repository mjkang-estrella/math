from pathlib import Path
import hashlib,json,subprocess,sys
B=Path(__file__).resolve().parents[2]
src=B/'lanes/sol-median-temporal-preliminary-review-r1'
dst=Path(__file__).resolve().parent/'private-replay'
bindings=[]
for rel in ['independent_check.py','frozen/certificate-results.json']:
    original=src/rel
    data=original.read_bytes()
    target=dst/rel
    target.parent.mkdir(parents=True,exist_ok=True)
    target.write_bytes(data)
    digest=hashlib.sha256(data).hexdigest()
    bindings.append({'original':str(original),'copy':str(target),'sha256':digest})
result=subprocess.run([sys.executable,'-B',str(dst/'independent_check.py')],capture_output=True,text=True,check=False)
for row in bindings:
    assert hashlib.sha256(Path(row['original']).read_bytes()).hexdigest()==row['sha256']
    assert hashlib.sha256(Path(row['copy']).read_bytes()).hexdigest()==row['sha256']
receipt={'exit_code':result.returncode,'stdout':result.stdout,'stderr':result.stderr,'bindings':bindings,'scope':'Root replay of independently written exact checker, not a Lean or complete packet audit.'}
(dst.parent/'replay-receipt.json').write_text(json.dumps(receipt,indent=2))
print(result.stdout.strip())
assert result.returncode==0,result.stderr
