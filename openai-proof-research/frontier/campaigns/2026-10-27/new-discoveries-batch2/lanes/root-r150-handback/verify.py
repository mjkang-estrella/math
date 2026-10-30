from pathlib import Path
import hashlib,json,shutil,subprocess,sys
P=Path(__file__).resolve().parent;S=P.parent/'sol-fresh-source-discovery-r150'
def sha(p):
 with p.open('rb') as f:return hashlib.file_digest(f,'sha256').hexdigest()
counts={}
for name in ['finalmanifest.json','scientific-freeze.json']:
 rows=json.loads((S/name).read_text())['entries']
 for r in rows:assert sha(S/r['path'])==r['sha256'],r['path']
 counts[name]=len(rows)
Q=P/'replay';Q.mkdir(exist_ok=True);shutil.copyfile(S/'checks.py',Q/'checks.py')
r=subprocess.run([sys.executable,str(Q/'checks.py')],check=True,capture_output=True,text=True)
(P/'replay.log').write_text(r.stdout+r.stderr);assert sha(Q/'checks.json')==sha(S/'checks.json')
j=json.loads((Q/'checks.json').read_text())
out={'status':'PASS','hash_counts':counts,'byte_identical_output':True,'numerator_comparisons':j['comparisons'],'eligible_parameters':j['eligible_parameters'],'square_records':len(j['a_n_square_records']),'local_controls':len(j['local_controls']),'universal_stability_proof':False,'credit':0}
(P/'replay-receipt.json').write_text(json.dumps(out,indent=2)+'\n');print(json.dumps(out))
