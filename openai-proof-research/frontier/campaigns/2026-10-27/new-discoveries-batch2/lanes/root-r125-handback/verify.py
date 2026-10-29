from pathlib import Path
import hashlib,json,shutil,subprocess,sys
P=Path(__file__).resolve().parent; B=P.parents[1]; S=P.parent/'sol-fresh-source-discovery-r125'
def sha(p):
 h=hashlib.sha256()
 with p.open('rb') as f:
  for c in iter(lambda:f.read(1048576),b''):h.update(c)
 return h.hexdigest()
m=json.loads((S/'finalmanifest.json').read_text())['files']
def verify():
 for r in m:assert sha(S/r['path'])==r['sha256'] and (S/r['path']).stat().st_size==r['bytes'],r['path']
verify()
for n in ['checks.py','research.py']:shutil.copy2(S/n,P/n)
r=subprocess.run([sys.executable,str(P/'checks.py')],capture_output=True,text=True,check=True)
(P/'checks.log').write_text(r.stdout+r.stderr)
j=json.loads((P/'check-results.json').read_text());old=json.loads((S/'check-results.json').read_text())
assert j['equivalence_checks']==old['equivalence_checks'] and j['merge_obstruction']==old['merge_obstruction']
assert sum(x['colorings'] for x in j['equivalence_checks'])==92913
lock=json.loads((S/'source-lock.json').read_text())['files']
for r in lock:assert sha(S/r['path'])==r['sha256']
verify()
(P/'ADOPTION.json').write_text(json.dumps({'status':'UNRESOLVED','credit':0,'counts':[9,39],'manifest_entries':len(m),'scientific_source_hashes':len(lock),'copied_checker_replay':'PASS','assignments':92913,'failed_global_color_merges':6,'qualification':'Copied diagnostic implementation, not an independent checker or universal admissibility proof. Source/registry coverage limits retained.'},indent=2)+'\n')
print((P/'ADOPTION.json').read_text())
