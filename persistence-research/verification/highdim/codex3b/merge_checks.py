import sys
sys.dont_write_bytecode=True
import pathlib,json,hashlib,os,collections
HERE=pathlib.Path(__file__).resolve().parent;ROOT=HERE.parents[2]
paths=['checker_results.json','checker_results_extra_v14.json','checker_results_extra_hd103.json','checker_results_extra_hd112.json']
checks={}
for fn in paths:
 data=json.load(open(HERE/fn))
 for key,v in data.items():
  if key in checks:assert checks[key]['certificate_sha256']==v['certificate_sha256']
  assert v['status']=='PASS',(key,v['status'])
  assert hashlib.sha256((ROOT/v['checker']).read_bytes()).hexdigest()==v['checker_sha256']
  checks[key]=v
certs=sorted((HERE/'certs').rglob('*.jsonl'))
for p in certs:
 for kind in ('hd','v14'):
  v=checks[str(p.relative_to(HERE))+'::'+kind]
  assert v['status']=='PASS' and v['certificate_sha256']==hashlib.sha256(p.read_bytes()).hexdigest()
assert len(checks)==2*len(certs)
tmp=str(HERE/'checker_results.json.tmp');json.dump(checks,open(tmp,'w'),indent=1);os.replace(tmp,HERE/'checker_results.json')
print('MERGED CHECKS',len(checks),'PASS for',len(certs),'certificates')
