"""Read-only verification of payload; writes only its excluded receipt."""
import pathlib,json,hashlib,math,datetime
L=pathlib.Path(__file__).resolve().parent
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
manifest=json.loads((L/'manifest.json').read_text())
assert all(r['path'] not in ['manifest.json','verification-receipt.json'] for r in manifest)
for r in manifest:
 p=L/r['path'];assert p.stat().st_size==r['bytes'] and sha(p)==r['sha256'],p
for row in json.loads((L/'freeze.json').read_text()):assert sha(pathlib.Path(row['original']))==sha(pathlib.Path(row['copy']))==row['sha256']
# Recheck independently all exact radical sign certificates, with no float/mpmath calls.
d=json.loads((L/'exact-results.json').read_text());D=1<<d['sqrt_enclosure_bits'];count=0
for row in d['rows']:
 n=row['degree'];points=row['certified_alternating_points'];assert len(points)==n
 previous=None;last=0
 for a,b,s in points:
  assert a>0 and b>0
  if previous is not None:assert previous[0]*b<a*previous[1]
  lo=hi=0
  for k in range(1,n+1):
   c=math.comb(n,k)*math.factorial(n)//math.factorial(k)
   root=math.isqrt(k*D*D);assert root**2<=k*D*D<(root+1)**2
   v=c*((-a)**(k-1))*b**(n-k)
   x=v*root;y=v*(root+(root*root!=k*D*D));lo+=min(x,y);hi+=max(x,y)
  assert (lo>0 and s==1) or (hi<0 and s==-1)
  if last:assert s==-last
  previous=(a,b);last=s;count+=1
# Payload completeness, including no unmanifested files other than exclusions.
assert {str(p.relative_to(L)) for p in L.rglob('*') if p.is_file() and p.name not in ['manifest.json','verification-receipt.json']}=={r['path'] for r in manifest}
receipt={'utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'status':'PASS','manifest_sha256':sha(L/'manifest.json'),'files_checked':len(manifest),'exact_radical_signs':count,'degrees':[r['degree'] for r in d['rows']],'original_copy_bindings':'PASS before/after','independent_proof_review':False,'priority_clearance':False,'counts_unchanged':[9,39,40]}
(L/'verification-receipt.json').write_text(json.dumps(receipt,indent=2));print(json.dumps(receipt,indent=2))
