from pathlib import Path
import hashlib,json,shutil,subprocess,sys
P=Path(__file__).resolve().parent; B=P.parents[1]
def sha(p):
 h=hashlib.sha256()
 with p.open('rb') as f:
  for c in iter(lambda:f.read(1048576),b''):h.update(c)
 return h.hexdigest()
out={}
for n in [126,127]:
 S=P.parent/f'sol-fresh-source-discovery-r{n}';D=P/f'copy-r{n}';D.mkdir(exist_ok=True)
 raw=json.loads((S/'finalmanifest.json').read_text())['files']
 m=raw if isinstance(raw,dict) else {r['path']:r['sha256'] for r in raw}
 for p,h in m.items():assert sha(S/p)==h,p
 if n==126:
  names={'checks.py','http.jsonl','source-lock.json','screen-receipt.json','screen.sqlite','pathmap.jsonl.gz'}
  for r in json.loads((S/'source-lock.json').read_text()):names.add(r['copy'])
  for line in (S/'http.jsonl').read_text().splitlines():names.add(json.loads(line)['copy'])
  check='checks.py'
 else:
  names={'check.py','context-receipts.json','original-receipts.json','http.jsonl'}
  for file in ['context-receipts.json','original-receipts.json']:
   for r in json.loads((S/file).read_text()):names.add(r['copy'])
  for line in (S/'http.jsonl').read_text().splitlines():
   r=json.loads(line)
   if 'copy' in r:names.add(r['copy'])
  check='check.py'
 for p in names:
  dst=D/p;dst.parent.mkdir(parents=True,exist_ok=True);shutil.copy2(S/p,dst)
 r=subprocess.run([sys.executable,str(D/check)],capture_output=True,text=True,check=True)
 (P/f'r{n}-checks.log').write_text(r.stdout+r.stderr)
 j=json.loads(r.stdout)
 if n==126:assert j['pass_all'] and j['finite_exact_algebra_checks']==39
 else:assert j['status']=='PASS' and j['residue_cases']==20 and j['negative_coefficients']==[[1,-1],[11,-1],[55,-1],[65,-1]]
 for p,h in m.items():assert sha(S/p)==h,p
 out[str(n)]={'manifest_entries':len(m),'copied_replay':'PASS','diagnostic_result':j,'credit':0}
out['counts']=[9,39];out['qualification']='Copied finite checkers only. No external Lean replay, full dependency audit, or novelty absence clearance.'
(P/'ADOPTION.json').write_text(json.dumps(out,indent=2)+'\n')
print(json.dumps({n:out[n]['manifest_entries'] for n in ['126','127']}))
