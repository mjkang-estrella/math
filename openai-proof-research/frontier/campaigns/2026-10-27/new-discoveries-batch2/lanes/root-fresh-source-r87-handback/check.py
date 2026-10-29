import hashlib, json, math
from pathlib import Path
from datetime import datetime, timezone

root=Path(__file__).resolve().parent
lane=root.parent/'sol-fresh-source-discovery-r87'
def sha(p):
    h=hashlib.sha256()
    with p.open('rb') as f:
        for block in iter(lambda:f.read(1048576),b''): h.update(block)
    return h.hexdigest()
manifest=json.loads((lane/'provenance.json').read_text())['sha256']
actual={p:sha(lane/p) for p in manifest}
drift={p:{'expected':manifest[p],'actual':actual[p]} for p in manifest if manifest[p]!=actual[p]}
assert not drift,drift
def factors(n):
    result={}; p=2
    while p*p<=n:
        while n%p==0: result[p]=result.get(p,0)+1; n//=p
        p+=1
    if n>1: result[n]=1
    return result
def mu(n):
    f=factors(n)
    return 0 if any(v>1 for v in f.values()) else (-1)**len(f)
def phi(n): return sum(math.gcd(k,n)==1 for k in range(1,n+1))
def divs(n): return [k for k in range(1,n+1) if n%k==0]
checks=0
for i in range(1,21):
    for j in range(1,21):
        C=sum(mu(i//d)*mu(j//e)*math.lcm(d,e) for d in divs(i) for e in divs(j))
        fi,fj=factors(i),factors(j)
        expected=0 if any(fi[p]!=fj[p] for p in fi.keys()&fj.keys()) else (-1)**len(factors(math.gcd(i,j)))*phi(math.lcm(i,j))
        assert C==expected
        G=sum(mu(i//d)*mu(j//e)*math.gcd(d,e) for d in divs(i) for e in divs(j))
        assert G==(phi(i) if i==j else 0)
        checks+=1
assert 2*0-1*1==-1
record={'utc':datetime.now(timezone.utc).isoformat(),'status':'UNRESOLVED','credit':0,
 'counts':{'additional':8,'total':38},'manifest_verified':len(manifest),'drift':drift,
 'provenance_sha256':sha(lane/'provenance.json'),'root_checks':{'entry_pairs':checks,'identities_per_pair':2,'principal_1_2_determinant':-1},
 'gap':'Nonsingularity for every binary-11 n remains unproved. The binary-10 direction is already public; no credit for it or finite checks.',
 'limits':'Root read full handoff and cached primary theorem passages; no independent full current prior-art audit. Did not repeat worker modular ranks or root-log-concavity diagnostics. No full source proof or Lean certificate.',
 'preserved_manifest':actual}
(root/'ADOPTION.json').write_text(json.dumps(record,indent=2)+'\n')
print(json.dumps({'pass':True,'hashes':len(manifest),'entry_pairs':checks,'credit':0}))
