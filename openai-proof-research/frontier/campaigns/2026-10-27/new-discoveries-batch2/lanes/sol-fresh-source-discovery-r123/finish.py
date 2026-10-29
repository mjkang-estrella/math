from pathlib import Path
import sys,json,hashlib,subprocess,time,gzip,re
L=Path(__file__).resolve().parent
def sha(b):return hashlib.sha256(b).hexdigest()
def dump(n,x):(L/n).write_text(json.dumps(x,indent=2)+'\n')
if sys.argv[1]=='metadata':
 B=L.parent.parent;R=L.parents[5]
 rec=[]
 paths=[B/'lanes/root-beta-prime-review-adoption-r1.md',B/'lanes/pi-beta-prime-classical-review-r1/review.md',B/'lanes/sol-fresh-analysis-discovery-r5/discovery.md',B/'lanes/sol-fresh-source-discovery-r97/discovery.md',B/'lanes/sol-fresh-source-discovery-r119/sources/omega-delta.json']
 for i,p in enumerate(paths):
  if not p.is_file():rec.append({'original':str(p),'missing':True});continue
  data=p.read_bytes();dest=L/'sources'/('additional-context-%02d'%i+p.suffix);dest.write_bytes(data)
  rec.append({'original':str(p),'copy':str(dest.relative_to(L)),'bytes':len(data),'sha256':sha(data),'utc':time.strftime('%Y-%m-%dT%H:%M:%SZ',time.gmtime())})
 dump('additional-context-receipts.json',rec)
 screen=json.loads((L/'screen-receipt.json').read_text());target=json.loads((L/'target-receipt.json').read_text())
 guard=B/'lanes/sol-edge-irregulator-manuscript-packet-r1/packet/helper_guard.py'
 dump('provenance.json',{'status':'NO ELIGIBLE CANDIDATE','credit':0,'counts_observed_only':{'additional':9,'total':39},'solo':True,'writes':'Assigned r123 lane only','guard':{'path':str(guard),'sha256':sha(guard.read_bytes()),'AS_groupRSS_MiB':512,'CPU_s':210,'wall_s':230,'nominal_sample_ms':40,'BLAS_threads':1,'limits':'Sampled RSS does not bound unsampled transients'},'history':{'paths':screen['paths'],'unique':screen['unique'],'broad_matching_bodies':screen['matching_bodies'],'target':target,'gaps_file':'screen-receipt.json','lexical_not_semantic_clearance':True},'registries':{'renyi':'Actual r4 review/exactcoverage retained: fixed 0d4df45 to d254db, 9 first-parent steps, 28 commits, 538 paths; mainline not every transient side branch; selective baseline semantics','factorial':'Actual final review and fresh-coverage retained: 12 steps to c3e8754; root strict exclusion adopted','r119':'22:21:24 observation at a7769c386bd6072628a21cf4680756d2a49bf221; d254 to a776 47 commits/207 paths uncapped but no all-body semantic clearance','OpenAI':'Inherited unchanged 7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a; no fresh head query','refresh':'Only meaningful bounded refresh: actual Krasniqi proof body at fixed r119 observed head; byte identical to old actual body. No worldwide priority or completeness claim'},'network':'Public read-only HTTP/search. One 403 retained without retry/bypass. No browser/accounts/messages/posts/uploads.','coordination':'coordination-NEXT-as-read.md plus separate receipt; not a mathematical freeze','formal':'No Lean or manuscript; no PROOF.md because no eligible full candidate','failure_limits':['Initial combined context display truncated; retained byte copies and bounded targeted reads used; no full semantic read of ledger/catalogue/tree claimed','Some console outputs truncated; exact receipts and files retained','Poppler alzer source warned of font-type mismatch; extracted mathematical text coherent; no visual-source verification claimed','Focused report is based on bounded first-five excerpts, so absence there is not a comprehensive history clearance']})
 dump('source-lock.json',{'http':[json.loads(x) for x in (L/'http.jsonl').read_text().splitlines()],'local_context':rec})
 print({'history_paths':screen['paths'],'unique':screen['unique'],'gap_entries':len(screen['gaps']),'excluded_names':screen['excluded_names'],'target':target})
elif sys.argv[1]=='focus':
 rg=re.compile(r'03505-9|Xu.{0,8}Yang|2609[.]28707|boundary.contact.uniqueness|Krasniqi|beta.prime.addition|Conjecture.?7[.]1',re.I)
 rows=[]
 for line in (L/'target-matches.jsonl').read_text().splitlines():
  x=json.loads(line)
  if rg.search(x['path']) or any(rg.search(v[1]) for v in x['matches']):rows.append(x)
 dump('focused-history.json',rows)
 hashes={x['sha256'] for x in rows};aliases=[]
 with gzip.open(L/'pathmap.jsonl.gz','rt') as f:
  for line in f:
   h,p=json.loads(line)
   if h in hashes:aliases.append([h,p])
 dump('focused-aliases.json',aliases)
 print([(x['path'],x['count']) for x in rows])
elif sys.argv[1]=='seal':
 r=subprocess.run([sys.executable,str(L/'checks.py')],capture_output=True,text=True,check=True)
 (L/'checks-receipt.json').write_text(r.stdout)
 files={str(p.relative_to(L)):{'sha256':sha(p.read_bytes()),'bytes':p.stat().st_size} for p in sorted(L.rglob('*')) if p.is_file() and p.name not in {'finalmanifest.json','manifest-verification.json'}}
 dump('finalmanifest.json',{'utc':time.strftime('%Y-%m-%dT%H:%M:%SZ',time.gmtime()),'files':files,'exclusions':['finalmanifest.json','manifest-verification.json'],'scope':'Assigned lane bytes only; coordination snapshot distinguished by name; no shared context freeze asserted'})
elif sys.argv[1]!='verify':raise ValueError(sys.argv)
if sys.argv[1] in ('seal','verify'):
 m=json.loads((L/'finalmanifest.json').read_text());errors=[]
 for n,r in m['files'].items():
  p=L/n
  if not p.is_file() or p.stat().st_size!=r['bytes'] or sha(p.read_bytes())!=r['sha256']:errors.append(n)
 actual={str(p.relative_to(L)) for p in L.rglob('*') if p.is_file() and p.name not in m['exclusions']}
 assert actual==set(m['files']) and not errors
 r={'status':'PASS','files':len(actual),'manifest_sha256':sha((L/'finalmanifest.json').read_bytes()),'errors':errors}
 if sys.argv[1]=='seal':dump('manifest-verification.json',r)
 print(json.dumps(r))
