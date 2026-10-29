import datetime,hashlib,json
from fractions import Fraction as F
from pathlib import Path
P=Path(__file__).resolve().parent;B=P.parent.parent;S=P.parent/'sol-fresh-source-discovery-r81'
def sha(p):
 h=hashlib.sha256()
 with p.open('rb') as f:
  for b in iter(lambda:f.read(1048576),b''):h.update(b)
 return h.hexdigest()
prov=json.loads((S/'provenance.json').read_text())
mismatches={name:{'recorded':h,'actual':sha(S/name)} for name,h in prov['artifact_hashes'].items() if sha(S/name)!=h}
assert set(mismatches)=={'finalize.log'}
assert mismatches['finalize.log']['recorded']==hashlib.sha256(b'').hexdigest()
# Independently sum cross-sections instead of enumerating 2-D points.
for m in (1,2,3,4,8,16,32,64):
 N=sum(2*(m-abs(x))+1 for x in range(-m,m+1))
 second=sum(x*x*(2*(m-abs(x))+1) for x in range(-m,m+1))
 assert N==2*m*m+2*m+1
 discrete=F(second,N);continuous=F(m*m,6)
 assert discrete==F(m*(m+1)*(m*m+m+1),3*N)
 assert 0<discrete-continuous<=F(m+1,6)
 # Exact induced vertex law in uniform unit-interval triangulation.
 weights={i:(F(1,4*m) if abs(i)==m else F(1,2*m)) for i in range(-m,m+1)}
 assert sum(weights.values())==1
 assert sum(i*i*w for i,w in weights.items())==F(m*m,3)+F(1,6)
 assert F(sum(i*i for i in weights),2*m+1)==F(m*(m+1),3)
assert F(1,4)**2<F(1,2)*F(1,4)
# Kernel smoothing equality would require b=0; test coefficient identity exactly.
assert (2-2,1-4)==(0,-3)
delta=json.loads((S/'sources/omega-delta-live').read_text())
assert delta['status']=='ahead' and delta['total_commits']==5
assert len(delta['files'])==2 and all(f['filename'].startswith('docs/') for f in delta['files'])
out={'utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'status':'UNRESOLVED','credit':0,'counts':[8,38],
 'source':'FGR published Question42 / arXiv2401.15462v4 Question40',
 'root_read':'Full worker SUMMARY/discovery; actual cached question passages; exact checks and saved compare response.',
 'matching_artifacts':len(prov['artifact_hashes'])-len(mismatches),'manifest_mismatches':mismatches,
 'manifest_qualification':'Initial root integrity check failed on finalize.log: worker hashed its then-empty output before writing its final summary. All other manifest entries match. Original bytes and stale manifest preserved; root records actual final log hash. This is not an all-hashes-match result.',
 'root_exact_checks':'Eight cross-section diamond sums and eight interval vertex-law identities; jitter midpoint inequality and smoothing polynomial obstruction.',
 'mathematical_gap':'Canonical tent coupling controls its induced vertex law w, not prescribed lattice p. Uniform geometry, weight discrepancy, support limits and literal extension conditions remain unproved. Same-scale covariance approximation is only a sufficient stronger target, not the source question itself.',
 'scope':'No theorem about all legal extensions is obtained. Diagnostic construction failures are not source refutations; symmetric examples are not general proofs.',
 'registry':'Saved compare response confirms five commits/two documentation paths from coherent root inventory to worker-observed e50b06adbf73bc8eaa5ae905ad0d7b0d178fe377. Root checked saved response, not a new remote observation. No universal novelty clearance.',
 'resource_qualification':'Worker retained MemoryError without raising cap. Its copied older capped_run.py does not self-limit supervisor; do not adopt an all-process-compliance claim. Root check uses improved self-limited helper guard.',
 'historical_counts':'Worker7/37 disk observation is historical; authoritative ledger now8/38.',
 'summary_sha256':sha(S/'SUMMARY.md'),'discovery_sha256':sha(S/'discovery.md')}
(P/'ADOPTION.json').write_text(json.dumps(out,indent=2)+'\n')
n=(B/'NEXT.md').read_text().replace('fresh analysis/probability r81, finite/arithmetic r82, and structural/geometric r83.','fresh analysis/probability r84, finite/arithmetic r82, and structural/geometric r83.')
marker='r79 lasso separation'
assert marker in n
n=n.replace(marker,'r81 FGR lattice-extension Question42/40 remains unresolved. Root exact interval vertex-law and diamond cross-section checks confirm helper identities only; uniform extension covariance control is missing. See root-fresh-source-r81-handback/ADOPTION.json.\n'+marker,1)
(B/'NEXT.md').write_text(n)
paths=[p for p in S.rglob('*') if p.is_file() and '__pycache__' not in p.parts]
paths.extend([P/'check.py',P/'ADOPTION.json',P/'pathspec.txt',B/'NEXT.md'])
(P/'pathspec.txt').write_text(''.join(str(p.relative_to(B.parents[4]))+'\n' for p in sorted(paths)))
print(json.dumps({'status':'scoped checks PASS; unresolved','artifacts':len(prov['artifact_hashes']),'counts':[8,38]}))
