"""One-shot sealer; never called by the read-only verifier."""
import pathlib,json,hashlib,datetime
R=pathlib.Path(__file__).resolve().parents[3];S=R/'frontier/sources/i79_logarithmic_girth_spectra_novelty_r3';E=R/'frontier/experiments/i79_logarithmic_girth_spectra_novelty_r3';P=R/'frontier/reviews/i79-logarithmic-girth-spectra-novelty-r3.md'
assert not (S/'seal-v1.json').exists(),'Never refresh a seal'
result=json.loads((E/'preseal-verification.json').read_text());assert result['status']=='PASS_EVIDENCE_AND_EXACT_BOOKKEEPING_ONLY'
exclude={str(S.relative_to(R)/'seal-v1.json'),str(E.relative_to(R)/'verification.json')}
paths={P}|{p for d in (S,E) for p in d.rglob('*') if p.is_file()}
rows=[]
for p in sorted(paths):
 rel=str(p.relative_to(R))
 if rel in exclude:continue
 b=p.read_bytes();rows.append(dict(path=rel,bytes=len(b),sha256=hashlib.sha256(b).hexdigest()))
seal=dict(version=1,created_utc=datetime.datetime.now(datetime.timezone.utc).isoformat(),scope='Independent conditional contribution review; provenance/finite checks are not original-proof verdicts',mutable_ledgers=sorted(['README.md','frontier/README.md','frontier/TEN-FINDINGS.md','frontier/iterations/README.md']),exclusions=sorted(exclude),artifacts=rows)
b=(json.dumps(seal,indent=2,sort_keys=True)+'\n').encode();(S/'seal-v1.json').write_bytes(b)
print(json.dumps({'sealed_artifacts':len(rows),'seal_sha256':hashlib.sha256(b).hexdigest(),'total_artifact_bytes':sum(x['bytes'] for x in rows)},indent=2))
