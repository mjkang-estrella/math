import json,hashlib,math,datetime
from pathlib import Path
P=Path(__file__).resolve().parent;B=P.parent.parent;src=P.parent/'sol-fresh-source-discovery-r73';cwd=B.parents[4]
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
prov=json.loads((src/'provenance.json').read_text())
manifest=next(v for v in prov.values() if isinstance(v,dict) and 'SUMMARY.md' in v)
bad=[name for name,h in manifest.items() if sha(src/name)!=h]
frozen={str(f.relative_to(src)):sha(f) for f in sorted(src.rglob('*')) if f.is_file() and '__pycache__' not in f.parts}
def works(n,m): return math.gcd(m*(n-1)+1,math.comb(m*n*n,m*n))==1
def prime(n):return n>=2 and all(n%d for d in range(2,math.isqrt(n)+1))
assert not any(prime(19*m+1) for m in range(2,9))
assert works(20,2)
assert [m for m in range(1,11) if works(32,m)]==[10]
assert (16%3<=128%3) and (16%9>128%9)
assert not works(8,2) and works(8,4)
equivalences=0
for n in range(2,30):
 for m in range(2,40):
  if prime(m*(n-1)+1):
   assert works(n,m)==(m<=n)
   equivalences+=1
result={'utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'status':'UNRESOLVED_PRESERVED','credit':0,'counts':[7,37],'source_scope':'Sun OEIS A390107: every n>=1 admits m<=floor(sqrt(3n+4)) with gcd(m(n-1)+1,binom(m*n*n,m*n))=1.','gap':'Uniform short-menu carry avoidance remains unproved.','root_read':'Completed thread, SUMMARY.md and complete discovery.md; no fresh primary-source body audit.','root_exact_checks':{'n20_composite_menu_success':True,'n32_least_m':10,'n8_higher_power_obstruction':True,'prime_modulus_equivalences':equivalences},'worker_scan_not_root_replayed':'n through100000 and full large checker suite are worker reports only.','manifest_entries':len(manifest),'manifest_mismatches':bad,'frozen_files':frozen,'freshness_note':'Worker scope used older snapshot; later root17:20UTC complete inventories are available but not applied here to claim full Sun novelty clearance.','holds':['full ordinary proof','source access and registry coverage as documented'],'no_formal_or_acceptance_claim':True}
(P/'ADOPTION.json').write_text(json.dumps(result,indent=2)+'\n')
nf=B/'NEXT.md';text=nf.read_text()
text=text.replace('Active Sol high/default: edge-irregulator current-prior r2, fresh arithmetic/algebra r73,','r73 Sun binomial-coprimality remains unresolved; exact carry/prime-menu\nobstructions and limited root checks preserved in root-fresh-source-r73-handback.\nActive Sol high/default: edge-irregulator current-prior r2, fresh finite/algebra r75,')
nf.write_text(text)
paths=[str(f.relative_to(cwd)) for folder in (src,P) for f in sorted(folder.rglob('*')) if f.is_file() and '__pycache__' not in f.parts and f.name!='pathspec.txt']
paths.append(str(nf.relative_to(cwd)))
(P/'pathspec.txt').write_text('\n'.join(paths)+'\n')
print(json.dumps({k:v for k,v in result.items() if k!='frozen_files'}))
