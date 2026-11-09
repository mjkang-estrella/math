from pathlib import Path
import hashlib,json,datetime,os,subprocess,sys
R=Path(__file__).resolve().parents[1]
P=R.parents[3]
A=P/'frontier/campaigns/2026-10-14/fresh-structural-discovery-r143'
E={'FINAL.json','MANIFEST.json','REPORT.md','SHA256SUMS'}
def sha(b):return hashlib.sha256(b).hexdigest()
def dump(p,o):p.write_text(json.dumps(o,indent=2,ensure_ascii=False)+'\n')
if any((R/n).exists() for n in ['FINAL.json','MANIFEST.json','SHA256SUMS']):raise RuntimeError('already sealed')
before=json.loads((R/'private/incoming-before.json').read_text())
after={str(p.relative_to(A)):sha(p.read_bytes()) for p in A.rglob('*') if p.is_file()}
changes=[{'path':n,'before':before.get(n),'now':after.get(n)} for n in sorted(set(before)|set(after)) if before.get(n)!=after.get(n)]
named=[]
for x in json.loads((R/'private/current-originals.json').read_text())['files']:
 b=(P/x['original']).read_bytes();h=sha(b)
 row={'path':x['original'],'captured_sha256':x['sha256'],'current_sha256':h,'equal_now':h==x['sha256']}
 if h!=x['sha256']:
  out=R/'private/current-originals-at-seal'/x['original'];out.parent.mkdir(parents=True,exist_ok=True);out.write_bytes(b);row['new_capture']=str(out.relative_to(R))
 named.append(row)
dump(R/'private/current-observation.json',{'observed':datetime.datetime.now(datetime.timezone.utc).isoformat(),'incoming_root_files_before':len(before),'incoming_root_files_now':len(after),'incoming_changes':changes,'named_originals':named,'meaning':'Present bytes only, compared with late review snapshots; no first-read or whole-parent/history guarantee. No incoming mutation was authorized or performed.'})
if changes:raise RuntimeError('incoming current bytes differ; inspect before disposition seal')
for p in [R/'packet/public/review.md',R/'REPORT.md',R/'private/mathematical-notes.md']:
 if 'TECHNICAL' not in p.read_text():raise RuntimeError('missing disposition')
rows=[]
for d,ds,fs in os.walk(R,followlinks=False):
 for n in ds+fs:
  if (Path(d)/n).is_symlink():raise RuntimeError('symlink')
 for n in fs:
  p=Path(d)/n;rel=p.relative_to(R).as_posix()
  if rel in E:continue
  b=p.read_bytes();rows.append({'path':rel,'bytes':len(b),'sha256':sha(b)})
rows.sort(key=lambda x:x['path'])
dump(R/'MANIFEST.json',{'format':'t177c143-contribution-r1-exact-v1','meaning':'Exact inventory of all local review payload files, including private protected bodies under original rights. Only four root envelopes excluded. No publication right or mathematical verdict follows from hashes.','envelopes':sorted(E),'files':rows})
f={'candidate':'T177C143','role':'first independent substantial-contribution review','disposition':'TECHNICAL','conditional_on_correctness':True,'correctness_verdict':'NOT ASSIGNED','scope':'ENTIRE immutable incoming frozen theorem, all finite A/B, all nonlinear stochastic sections/grand couplings, every source dimension/allowed odd prime/level, finite C, both constants and separation','runner':'Codex / GPT-6.1-Sol / high / default service tier','publication':'STOPPED','sealed':datetime.datetime.now(datetime.timezone.utc).isoformat(),'manifest_sha256':sha((R/'MANIFEST.json').read_bytes()),'report_sha256':sha((R/'REPORT.md').read_bytes()),'review_path':'packet/public/review.md','review_sha256':sha((R/'packet/public/review.md').read_bytes()),'verifier_path':'packet/public/verify.py','verifier_sha256':sha((R/'packet/public/verify.py').read_bytes()),'incoming_frozen_scope_sha256':'cc916afef1373c1b3c0abdee271a4c2769f887f664e8c9b2b16b1b381c0de221','payload_files':len(rows),'incoming_root_unchanged_at_check':not changes,'named_originals_equal_at_check':sum(x['equal_now'] for x in named),'named_originals_compared':len(named),'limitations':'Bounded primary/transitive/history coverage; first traversal and derivative-admission errors explicit; no perfect isolation/priority/history or other gate. Current-original captures late. Artifact controls not mathematics.'}
dump(R/'FINAL.json',f)
h={n:sha((R/n).read_bytes()) for n in ['FINAL.json','MANIFEST.json','REPORT.md']}
(R/'SHA256SUMS').write_text(''.join(h[n]+'  '+n+'\n' for n in h))
cmd=[sys.executable,str(R/'packet/public/verify.py'),str(R)]
for n,flag in [('FINAL.json','--final-sha256'),('MANIFEST.json','--manifest-sha256'),('REPORT.md','--report-sha256')]:cmd.extend([flag,h[n]])
r=subprocess.run(cmd,capture_output=True,text=True,timeout=30,env={**os.environ,'PYTHONDONTWRITEBYTECODE':'1','TMPDIR':str(R/'work')})
print(r.stdout,r.stderr)
if r.returncode:raise RuntimeError('sealed verification failed')
print('Original incoming files unchanged:',len(after));print('Named originals equal:',sum(x['equal_now'] for x in named),'/',len(named));print((R/'SHA256SUMS').read_text())
