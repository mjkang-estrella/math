"""Seal once, after author checks. Never overwrite an existing seal."""
import pathlib,datetime,json,hashlib
R=pathlib.Path(__file__).resolve().parents[3]
S=R/'frontier/sources/i76_logarithmic_girth_spectra'
E=R/'frontier/experiments/i76_logarithmic_girth_spectra'
target=S/'seal-v1.json'
assert not target.exists(),'Existing seal is immutable; preserve and version any correction explicitly.'
exclude={target,E/'verification.json'}
paths={R/'frontier/iterations/i76-logarithmic-girth-spectra.md'}|{p for base in (S,E) for p in base.rglob('*') if p.is_file() and p not in exclude}
artifacts=[]
for p in sorted(paths):
 b=p.read_bytes();artifacts.append(dict(path=str(p.relative_to(R)),bytes=len(b),sha256=hashlib.sha256(b).hexdigest()))
data=dict(version=1,sealed_utc=datetime.datetime.now(datetime.timezone.utc).isoformat(),
 mutable_ledgers=sorted(['README.md','frontier/README.md','frontier/TEN-FINDINGS.md','frontier/iterations/README.md']),
 exclusions=sorted(str(p.relative_to(R)) for p in exclude),artifacts=artifacts,
 meaning='Immutable author evidence seal, not independent proof approval or contribution approval.')
target.write_text(json.dumps(data,indent=2)+'\n');print(json.dumps({'sealed_artifacts':len(artifacts),'seal_sha256':hashlib.sha256(target.read_bytes()).hexdigest()}))
