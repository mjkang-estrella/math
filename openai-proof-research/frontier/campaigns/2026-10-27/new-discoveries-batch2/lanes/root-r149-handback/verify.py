from pathlib import Path
import hashlib,json,shutil,subprocess,sys
P=Path(__file__).resolve().parent;S=P.parent/'sol-fresh-source-discovery-r149'
def sha(p):
 with p.open('rb') as f:return hashlib.file_digest(f,'sha256').hexdigest()
counts={}
for name in ['finalmanifest.json','scientific-freeze.json']:
 rows=json.loads((S/name).read_text())['files']
 for r in rows:assert sha(S/r['path'])==r['sha256'],r['path']
 counts[name]=len(rows)
Q=P/'replay';Q.mkdir(exist_ok=True);shutil.copyfile(S/'checks.py',Q/'checks.py')
r=subprocess.run([sys.executable,str(Q/'checks.py')],check=True,capture_output=True,text=True)
(P/'replay.log').write_text(r.stdout+r.stderr);assert sha(Q/'checks.json')==sha(S/'checks.json')
j=json.loads((Q/'checks.json').read_text())
out={'status':'PASS','hash_counts':counts,'byte_identical_output':True,'all_deletion_sets':j['all_subsets_d5']['subsets'],'windmill_controls':len(j['windmills']),'single_edge_exchanges':sum(r['all_exchanges'] for r in j['strict_exchange']),'universal_leaf_distance_result':False,'credit':0}
(P/'replay-receipt.json').write_text(json.dumps(out,indent=2)+'\n');print(json.dumps(out))
