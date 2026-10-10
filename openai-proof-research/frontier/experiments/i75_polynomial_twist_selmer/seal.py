"""One-time author sealing. Verification uses verify.py, never this script."""
import pathlib,json,hashlib
R=pathlib.Path(__file__).resolve().parents[3]
S=R/'frontier/sources/i75_polynomial_twist_selmer';E=R/'frontier/experiments/i75_polynomial_twist_selmer';seal=S/'seal-v1.json'
assert not seal.exists(),'Refusing to refresh an existing immutable seal'
files=sorted([p for root in [S,E] for p in root.rglob('*') if p.is_file()]+[R/'frontier/iterations/i75-polynomial-twist-selmer.md'])
data={'version':1,'scope':'Evidence and finite reproduction only, not independent proof acceptance','files':{str(p.relative_to(R)):hashlib.sha256(p.read_bytes()).hexdigest() for p in files}}
seal.write_text(json.dumps(data,indent=2)+'\n')
print(json.dumps({'sealed_files':len(files),'seal_sha256':hashlib.sha256(seal.read_bytes()).hexdigest()}))
