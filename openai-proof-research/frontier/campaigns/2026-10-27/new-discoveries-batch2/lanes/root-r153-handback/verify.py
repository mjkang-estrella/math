from pathlib import Path
import hashlib,json,shutil,subprocess,sys
P=Path(__file__).resolve().parent;S=P.parent/'sol-fresh-source-discovery-r153'
def sha(p):
 with p.open('rb') as f:return hashlib.file_digest(f,'sha256').hexdigest()
counts={}
for name in ['finalmanifest.json','scientific-freeze.json']:
 rows=json.loads((S/name).read_text())['files']
 for path,h in rows.items():assert sha(S/path)==h,path
 counts[name]=len(rows)
Q=P/'replay';Q.mkdir(exist_ok=True);shutil.copyfile(S/'checks.py',Q/'checks.py')
r=subprocess.run([sys.executable,str(Q/'checks.py')],check=True,capture_output=True,text=True)
(P/'replay.log').write_text(r.stdout+r.stderr)
a=json.loads((S/'checks.json').read_text());b=json.loads((Q/'checks.json').read_text());a.pop('seconds');b.pop('seconds');assert a==b
out={'status':'PASS','hash_counts':counts,'equal_except_seconds':True,'degrees':b['source_degrees'],'rabin_trials':b['rabin_trials'],'independent_sympy_tests':b['independent_sympy_tests'],'local_factorization_tests':b['local_factorization_tests'],'frobenius_square_tests':b['frobenius_square_tests'],'universal_source_result':False,'credit':0}
(P/'replay-receipt.json').write_text(json.dumps(out,indent=2)+'\n');print(json.dumps(out))
