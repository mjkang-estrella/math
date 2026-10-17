"""Verify packet bytes and pinned source Git identities; not a proof checker."""
from pathlib import Path
import hashlib
import json
from fractions import Fraction as Q

base = Path(__file__).resolve().parent
repo = base.parents[3]
count = 0
for receipt in [base/'inputs/private/source-receipt.json', base/'inputs/private/perceptron/source-receipt.json']:
    for record in json.loads(receipt.read_text()):
        data = (repo/record['local']).read_bytes()
        assert hashlib.sha256(data).hexdigest() == record['sha256']
        assert hashlib.sha1(b'blob '+str(len(data)).encode()+b'\0'+data).hexdigest() == record['gitblob']
        count += 1
for record in json.loads((base/'inputs/private/primary/receipt.json').read_text()):
    data = (base/'inputs/private/primary'/(record['name']+'.pdf')).read_bytes()
    assert hashlib.sha256(data).hexdigest() == record['sha256']
assert Q(4,5)*Q(-1,2)+Q(1,5)*2 == 0
assert Q(4,5)*Q(1,4)+Q(1,5)*4 == 1
assert Q(3,16)/(2*Q(17,8)) == Q(3,68)
manifest = json.loads((base/'manifest.json').read_text())
for record in manifest['files']:
    assert hashlib.sha256((base/record['path']).read_bytes()).hexdigest() == record['sha256'], record['path']
print(f'Byte receipts verified: {count} pinned TeX inputs, 2 classical PDFs, {len(manifest["files"])} manifest payloads. Exact elementary construction constants agree. This is not a universal proof or contribution check.')
