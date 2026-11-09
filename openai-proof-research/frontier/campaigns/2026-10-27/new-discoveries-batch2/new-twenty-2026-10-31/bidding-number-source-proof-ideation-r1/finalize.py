import os,resource
os.sched_setaffinity(0,sorted(os.sched_getaffinity(0))[:2]);resource.setrlimit(resource.RLIMIT_CPU,(120,120));resource.setrlimit(resource.RLIMIT_AS,(6*1024**3,6*1024**3))
import pathlib,sys,subprocess,json,hashlib,time,threading,datetime
p=pathlib.Path(__file__).resolve().parent
samples=[];stop=threading.Event()
def sample():
 while not stop.is_set():
  samples.append(int(next(x for x in pathlib.Path('/proc/self/status').read_text().splitlines() if x.startswith('VmRSS:')).split()[1]));stop.wait(.02)
t=threading.Thread(target=sample);t.start();start=time.time()
def save(n,s):
 r=subprocess.run([sys.executable,'-I','-B',str(p/'write_lane.py'),n],input=s,text=True,capture_output=True,timeout=20);assert r.returncode==0
try:
 if sys.argv[1]=='inventory':
  base=p.parent/'expanded-corpus-r361'; files=['literals/355433.json','results.json','ORDINARY.md','VERSION-AND-ACCESS.md','source-inventory.json','local-source-inventory.json','sources/bidding.html.txt','sources/bidding-v1.html.txt','sources/bidding-companion.html.txt','sources/bidding-journal-record.html']
  depth=['Full literal','Only keyed 355433 entry reviewed','Only 355433 section reviewed; first initial substring probe hit introductory disclaimer','355433 and access/registry rules reviewed; unrelated portions surfaced incidentally','Inventory routing only; earlier output truncated','Routing only; no source theorem dependency inferred','Characters 0:41000 and Conjecture 68 surroundings, covering sections 1–7 and part of 8; later conjectures 68–73; not full body','Characters 2200:10500 and 40000:end; not full body','Characters 0:13000 and 22000:30000; actual auction, zero-budget and monotonicity passages; not full body','Only citation metadata, abstract and link-bearing lines; no journal body']
  inv=[]
  for f,d in zip(files,depth):
   data=(base/f).read_bytes();inv.append({'path':str(base/f),'bytes':len(data),'sha256':hashlib.sha256(data).hexdigest(),'actual_depth':d,'note':'Hash recorded now; not a retrospective resource sample for earlier reading'})
  root=p.parents[5]/'sources'
  # Use the explicit project path, without any historical recursive scan.
  root=pathlib.Path('/home/mj-kang/Documents/Dev/math/openai-proof-research/sources')
  routing=[]
  for f in ['upstream.json','CONTENTS.md','preprints-tree.json']:
   data=(root/f).read_bytes();s=data.decode();hits=[x for x in s.splitlines() if any(k in x.lower() for k in ['bidding','2207.11596','355433'])];routing.append({'path':str(root/f),'sha256':hashlib.sha256(data).hexdigest(),'bytes':len(data),'narrow_hits':hits,'depth':'Metadata/routing only; no theorem imported'})
  data=(base/'sources/openai-current-contents.md').read_bytes();routing.append({'path':str(base/'sources/openai-current-contents.md'),'sha256':hashlib.sha256(data).hexdigest(),'narrow_hits':[x for x in data.decode().splitlines() if any(k in x.lower() for k in ['bidding','2207.11596','355433'])],'depth':'Same current head independently observed; cached pinned catalogue only'})
  save('read-inventory.json',json.dumps({'historical_exact':inv,'classical':{'path':'sources/classical.pdf.txt','depth':'Extracted lines 169:195,294:495,650:705 including actual number interpolation, closure, totality proofs; Theorem 3.5 only routing, not dependency; some combined earlier output truncated, 3.2–3.4 reprinted separately'},'survey':{'path':'sources/survey.pdf.txt','depth':'Extracted lines 335:447 actual rule/order/comparison statements; no full-body review'},'reconciliation':{'path':'sources/reconciliation.html','depth':'Web tool intro and section 5 Definitions 5.1–5.3, Lemma 5.4 proof and Theorem 5.5 proof actually surfaced; surrounding 4.9–5.14 also surfaced; not full-body review'},'routing':routing,'historical_allowlist':'Exact r361/results.json checked as allowlisted after protected-name filter; no broad historical body scan','telemetry_limit':'Early capped shell probes have true tool exit receipts only; no persistent RSS samples then. No retrospective samples invented.'},indent=2))
  print(json.dumps(routing,indent=2)[:1500])
 elif sys.argv[1]=='manifest':
  names=['PROOF.md','REVIEW.md','review.json','read-inventory.json','source-inventory.json','access.json','access-second.json','access-third.json','bootstrap-receipt.json','frozen-before.json','frozen-after.json','source_work.py','source_work_second.py','source_work_third.py','finalize.py','sources/classical.pdf.txt','sources/survey.pdf.txt','sources/reconciliation.html','sources/openai-head.html','sources/leanpool-head.html','sources/journal-record.html']
  names+=['receipts/'+x.name for x in (p/'receipts').iterdir() if x.is_file()]
  names += [x.name for x in p.iterdir() if x.is_file() and x.name.startswith('receipt-finalize-')]
  rows=[]
  for n in names:
   data=(p/n).read_bytes();rows.append({'path':n,'bytes':len(data),'sha256':hashlib.sha256(data).hexdigest()})
  save('manifest.json',json.dumps(rows,indent=2));bad=[r['path'] for r in rows if hashlib.sha256((p/r['path']).read_bytes()).hexdigest()!=r['sha256']];save('manifest-verification.json',json.dumps({'verified':not bad,'count':len(rows),'mismatches':bad,'utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'scope':'Explicit generated outputs and bootstrap/frozen receipts; supplied verifier and author inputs excluded'},indent=2));print('Manifest',len(rows),'mismatches',bad)
finally:
 stop.set();t.join();r=resource.getrusage(resource.RUSAGE_SELF)
 # Receipt is outside its own manifest, avoiding a self-hash cycle.
 save('receipt-finalize-'+sys.argv[1]+'-'+str(time.time_ns())+'.json',json.dumps({'start':start,'end':time.time(),'cpu_self':r.ru_utime+r.ru_stime,'maxrss_self_kib':r.ru_maxrss,'sampled_self_rss_kib':max(samples,default=None),'sample_count':len(samples),'joined_writer_children':True,'group_peak_claimed':False,'caps_before_reads':True,'completed_finally':True},indent=2))
