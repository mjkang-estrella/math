from pathlib import Path
import hashlib,json,shutil,subprocess,sys
P=Path(__file__).resolve().parent;S=P.parent/'sol-fresh-source-discovery-r158'
def sha(p):
 with p.open('rb') as f:return hashlib.file_digest(f,'sha256').hexdigest()
def verify():
 counts={}
 for name in ['finalmanifest.json','scientific-freeze.json']:
  rows=json.loads((S/name).read_text())['files']
  for f,h in rows.items():assert sha(S/f)==h,f
  counts[name]=len(rows)
 return counts
before=verify();Q=P/'replay';Q.mkdir(exist_ok=True)
for f in ['checks.py','ribbon_route.py']:shutil.copyfile(S/f,Q/f)
for f in ['checks.py','ribbon_route.py']:
 r=subprocess.run([sys.executable,str(Q/f)],capture_output=True,text=True,check=True)
 (P/(f+'.log')).write_text(r.stdout+r.stderr)
for f in ['checks.json','schur-obstruction.json','independent-controls.json','ribbon-route.json']:
 assert (Q/f).read_bytes()==(S/f).read_bytes(),f
b=json.loads((Q/'checks.json').read_text());assert all(not r['negative'] for r in b['records'])
i=json.loads((Q/'independent-controls.json').read_text())
after=verify();assert before==after
out={'status':'PASS','before':before,'after':after,'four_output_files_byte_identical':True,'normalized_functions':len(b['records']),'source_en_controls':b['source_en_controls'],'orthogonal_controls':i['orthogonal_definition_controls'],'universal_proof':False,'credit':0}
(P/'replay-receipt.json').write_text(json.dumps(out,indent=2)+'\n');print(json.dumps(out))
