"""One-time exclusive seal creation, only after successful read-only prevalidation."""
from pathlib import Path
import json,hashlib
P=Path(__file__).resolve().parent
BASE=P.parents[2]
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def main():
    assert not (P/'seal.json').exists(),'never reseal'
    pre=json.loads((P/'prevalidation.json').read_text())
    assert pre['status']=='PASS' and pre['mode']=='prevalidate'
    assert pre['bindings']['inventory_sha256']==sha(P/'inventory.json')
    inv=json.loads((P/'inventory.json').read_text())
    for e in inv['files']:
        f=BASE/e['path'];assert sha(f)==e['sha256'] and f.stat().st_size==e['size']
    s=BASE/'frontier/sources/i168_cross_class_exchange'
    ex=json.loads((s/'external-bindings.json').read_text())['files']
    context=json.loads((s/'replay-policy.json').read_text())['context_only_exclusions']
    for e in ex:
        if e['path'] not in context:assert sha(BASE/e['path'])==e['sha256']
    result={'iteration':168,'creation':'exclusive-create exactly once after successful prevalidation','inventory_sha256':sha(P/'inventory.json'),'prevalidation_sha256':sha(P/'prevalidation.json'),'report_sha256':pre['bindings']['report_sha256'],'verifier_sha256':sha(P/'verify.py')}
    with (P/'seal.json').open('x') as f:json.dump(result,f,sort_keys=True,indent=2);f.write('\n')
    print(json.dumps({'seal_sha256':sha(P/'seal.json'),'status':'created once'},sort_keys=True))
if __name__=='__main__':main()
