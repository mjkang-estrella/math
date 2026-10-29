from pathlib import Path
import hashlib,json,shutil,subprocess,sys
P=Path(__file__).resolve().parent;out={}
def sha(p):
 h=hashlib.sha256()
 with p.open('rb') as f:
  for c in iter(lambda:f.read(1048576),b''):h.update(c)
 return h.hexdigest()
for n in [131,132]:
 S=P.parent/f'sol-fresh-source-discovery-r{n}';D=P/f'copy-r{n}';D.mkdir(exist_ok=True)
 m=json.loads((S/'finalmanifest.json').read_text())['files']
 for r in m:assert sha(S/r['path'])==r['sha256'] and (S/r['path']).stat().st_size==r['bytes']
 lock=json.loads((S/'scientific-freeze.json').read_text())['files']
 for r in lock:assert sha(S/r['path'])==r['sha256']
 names=['games.py','sustain.py'] if n==131 else ['checks.py']
 for name in names:shutil.copy2(S/name,D/name)
 for name in names:
  r=subprocess.run([sys.executable,str(D/name)]+(['checks'] if n==132 else []),capture_output=True,text=True,check=True)
  (D/(name+'.log')).write_text(r.stdout+r.stderr)
 if n==131:
  j=json.loads((D/'game-check-results.json').read_text());c=json.loads((D/'component-check-results.json').read_text())
  assert j==json.loads((S/'game-check-results.json').read_text()) and c==json.loads((S/'component-check-results.json').read_text())
  assert j['cases']==288 and len(c)==5
  assert all(3*r['total'][0]<=2*r['n'] for r in j['records'])
  assert all(7*r['ordinary'][0]<=3*r['n'] for r in j['records'] if r['type']=='tree')
  extra={'sampled_minimax_graphs':288,'component_checks':5}
 else:
  j=json.loads((D/'check-results.json').read_text());assert j==json.loads((S/'check-results.json').read_text()) and j['passed']
  assert j['pointwise_obstruction']['ratio']=='6/5'
  extra={'SK_route_diagnostics':'PASS','pointwise_ratio':'6/5','rare_trap_checks':len(j['rare_trap'])}
 for r in m:assert sha(S/r['path'])==r['sha256']
 out[str(n)]={'manifest_entries':len(m),'source_freeze_entries':len(lock),'copied_replay':'PASS','credit':0,**extra}
out['counts']=[9,39];out['qualification']='Copied diagnostics; no universal game bound, SK mixing proof, or source counterexample established.'
(P/'ADOPTION.json').write_text(json.dumps(out,indent=2)+'\n');print(json.dumps(out))
