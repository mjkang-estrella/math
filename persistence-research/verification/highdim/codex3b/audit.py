"""Read-only coverage replay, hashes and final status in this isolated directory."""
import sys
sys.dont_write_bytecode=True
import os,json,pathlib,hashlib,collections,itertools
HERE=pathlib.Path(__file__).resolve().parent;ROOT=HERE.parents[2];sys.path.insert(0,str(HERE))
import run_target
from hnt import vp
share=json.load(open(HERE/'share.json'))['keys'];base=json.load(open(HERE/'baseline.json'));res=json.load(open(HERE/'results_t14112.json'));checks=json.load(open(HERE/'checker_results.json')) if (HERE/'checker_results.json').exists() else {}
assert set(res)<=set(share)
coverage={};allcert=set();failures=[]
for key in share:
 v=base[key];r=res.get(key,{'status':'UNATTEMPTED'});expected={}
 for K,free in run_target.slices(9*v['S_low']-1,v['far']):
  ordered=len(free)<=2
  for coefs in run_target.orderings(free) if ordered else [free]:
   suffix=('o' if ordered else 'u')+('_'.join(map(str,coefs)) or 'none')
   fn=f"certs/t14112/c_S{v['S_low']}_K{K}_{suffix}.jsonl"
   expected[fn]=(K,list(coefs),max(3,vp(K,2)+1) if free else vp(K,2)+1,'ordered' if ordered else 'unordered')
 certified=[];validated=[]
 for fn,meta in expected.items():
  p=HERE/fn
  if not p.exists():continue
  m=json.loads(open(p).readline());assert (m['K'],m['coefs'],m['qmin'],m['domain'])==meta,(key,fn)
  allcert.add(fn);certified.append(fn);sha=hashlib.sha256(p.read_bytes()).hexdigest()
  if all(checks.get(fn+'::'+k,{}).get('status')=='PASS' and checks[fn+'::'+k]['certificate_sha256']==sha for k in ('hd','v14')):validated.append(fn)
 if r['status']=='CLOSED' and len(validated)!=len(expected):failures.append(key)
 coverage[key]={'status':r['status'],'expected_certificates':len(expected),'present_certificates':len(certified),'directly_validated_certificates':len(validated),'files':certified,'cover_floor_max':max(m[2] for m in expected.values())}
print('STATUS',collections.Counter(res.get(k,{}).get('status','UNATTEMPTED') for k in share))
print('CERTIFICATES',len(allcert),'CHECKS',collections.Counter(v['status'] for v in checks.values()),'FAILED_CLOSURES',failures)
json.dump(coverage,open(HERE/'coverage_summary.json','w'),indent=1)
manifest={str(p.relative_to(HERE)):hashlib.sha256(p.read_bytes()).hexdigest() for p in sorted(HERE.rglob('*')) if p.is_file() and p.name not in ('manifest.json',) and not p.name.endswith('.tmp')}
for p in [ROOT/'verification/highdim/codex/results_t14112.json',ROOT/'verification/highdim/codex/checkhd.py',ROOT/'verification/v14_checknd_hd.py',ROOT/'verification/indep/nt.py',ROOT/'verification/indep2/e_enum.py']:
 manifest['SOURCE:'+str(p.relative_to(ROOT))]=hashlib.sha256(p.read_bytes()).hexdigest()
json.dump(manifest,open(HERE/'manifest.json','w'),indent=1)
assert not failures,failures
