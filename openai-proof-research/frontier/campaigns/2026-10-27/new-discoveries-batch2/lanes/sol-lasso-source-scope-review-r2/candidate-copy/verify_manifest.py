import pathlib,json,hashlib
p=pathlib.Path(__file__).resolve().parent
m=json.loads((p/'SHA256.json').read_text())
assert all(hashlib.sha256((p/k).read_bytes()).hexdigest()==v for k,v in m.items())
print('PASS: stable artifact hashes')
