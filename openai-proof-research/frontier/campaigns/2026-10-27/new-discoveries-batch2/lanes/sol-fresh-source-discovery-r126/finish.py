import json,hashlib,time
from pathlib import Path
L=Path(__file__).resolve().parent;R=L.parents[5]
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
if __import__('sys').argv[1]=='collect':
 base=R/'frontier/campaigns/2026-10-26/new-discoveries/lanes/pi-euler-turan-final-review/fresh/trureturing'
 rec=[]
 for name in ['Defs','Result','Laplace','Measure','Stieltjes']:
  p=base/'D5/S3/Analytic/WallisRemainder'/f'{name}.lean';q=L/'sources'/f'cached-wallis-{name}.lean';q.write_bytes(p.read_bytes());rec.append(dict(original=str(p),copy=str(q.relative_to(L)),bytes=q.stat().st_size,sha256=sha(q)))
 for name in ['wallis.pdf','wallis.txt','salazar.pdf','salazar.txt','wallis-public-result.lean']:
  p=L/'sources'/name;rec.append(dict(copy=str(p.relative_to(L)),bytes=p.stat().st_size,sha256=sha(p)))
 (L/'source-lock.json').write_text(json.dumps(rec,indent=2)+'\n')
 # This compact catalogue reading preserves all accepted names/scopes and rejection metadata.
 out={}
 for n in ['02','03']:
  d=json.loads((L/'sources'/f'context-{n}.json').read_text());out[n]=d
 print('ledger counts',out['02']['accepted_count'],out['02']['total_accepted_count'])
 for n,d in out.items():
  for r in d.get('accepted',[]):print(n,r.get('number'),r.get('title'),r.get('scope'))
elif __import__('sys').argv[1]=='provenance':
 extra=[]
 for rel in ['root-beta-prime-addition-r19/CLASSICAL-REDUCTION.md','pi-beta-prime-classical-review-r1/review.md','sol-fresh-source-discovery-r47/discovery.md','sol-fresh-source-discovery-r49/SUMMARY.md','sol-fresh-source-discovery-r49/discovery.md']:
  p=L.parent/rel;dest=L/'sources'/('history-'+rel.replace('/','-'));dest.write_bytes(p.read_bytes());extra.append(dict(original=str(p),copy=str(dest.relative_to(L)),sha256=sha(dest),bytes=dest.stat().st_size))
 (L/'additional-context-receipts.json').write_text(json.dumps(extra,indent=2)+'\n')
 d=dict(utc=time.strftime('%Y-%m-%dT%H:%M:%SZ',time.gmtime()),role='solo research sub-agent',model='GPT-6.1 Sol',reasoning='high',service='default',credit=0,observed_counts={'additional':9,'total':39},status='no eligible nomination',scientific_source_receipts='source-lock.json',http_receipts='http.jsonl',context='context-receipts.json',mutable_coordination='coordination-receipt.json',stream='screen-receipt.json',exact_screen='exact-receipt.json',guard=dict(path=str(L.parent/'sol-edge-irregulator-manuscript-packet-r1/packet/helper_guard.py'),sha256=sha(L.parent/'sol-edge-irregulator-manuscript-packet-r1/packet/helper_guard.py'),AS_bytes=512*1024**2,group_RSS_bytes=512*1024**2,CPU_seconds=210,wall_seconds=230,nominal_sample_ms=40,BLAS_threads=1),registry={'fixed_omega_refresh':'a7769c386bd6072628a21cf4680756d2a49bf221','scope':'Wallis Result.lean only; no new HEAD','inherited_renyi_interval':'0d4df45->d254db:9steps/28commits/538paths','inherited_factorial_closure':'through c3e8754','r119_observation':'2026-10-29T22:21:24Z a7769c3;47commits/207paths uncapped metadata, not semantic clearance','openai_inherited_unchanged':'7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a'},limits=['No worldwide absence claim','Original Szabo full text unread','Ferreira CMUP timeouts; AMS truncated HTML, not PDF','No new full proof or mathematical obstruction for Volterra lead','No independent public Lean replay','First large console reads truncated; later selected bounded reads'],external_mutations=False,git_operations=False,children=False,browser=False,other_lane_writes=False)
 (L/'provenance.json').write_text(json.dumps(d,indent=2)+'\n')
elif __import__('sys').argv[1]=='seal':
 excluded={'finalmanifest.json','manifest-verification.json'}
 files={str(p.relative_to(L)):sha(p) for p in sorted(L.rglob('*')) if p.is_file() and p.name not in excluded}
 (L/'finalmanifest.json').write_text(json.dumps(dict(utc=time.strftime('%Y-%m-%dT%H:%M:%SZ',time.gmtime()),files=files,exclusions=sorted(excluded)),indent=2)+'\n')
