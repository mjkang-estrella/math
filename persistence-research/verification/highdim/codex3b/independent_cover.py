"""Independent E enumeration/slicing replay against local certificate domains."""
import sys
sys.dont_write_bytecode=True
import pathlib,json,collections,itertools,importlib.util,hashlib
HERE=pathlib.Path(__file__).resolve().parent;ROOT=HERE.parents[2]
p=ROOT/'verification/indep2/e_enum.py'
spec=importlib.util.spec_from_file_location('e_enum_independent',p);E=importlib.util.module_from_spec(spec);spec.loader.exec_module(E)
configs=E.configs(14112);lookup={f"{S}|{','.join(map(str,f))}":(S,f,v) for (S,f),v in configs.items() if len(f)>=3 and not v['dead40']}
share=json.load(open(HERE/'share.json'))['keys'];base=json.load(open(HERE/'baseline.json'));res=json.load(open(HERE/'results_t14112.json'))
assert set(share)<=set(lookup)
for k in share:assert base[k]['multiset']==list(lookup[k][2]['multiset'])
report={};maxfloor=0
for key,r in res.items():
 if r['status']!='CLOSED':continue
 S,far,_=lookup[key];K0=9*S-1;need=E.slices(K0,far)
 groups=collections.defaultdict(list)
 for fn in (HERE/'certs'/'t14112').glob(f'c_S{S}_*.jsonl'):
  meta=json.loads(open(fn).readline());groups[(meta['K'],tuple(sorted(meta['coefs'])))].append((str(fn.relative_to(HERE)),meta))
 def decode(K):
  delta=K-K0
  if delta<0 or delta%9:return None
  fixed={i:9*int(d) for i,d in enumerate(str(delta//9)[::-1]) if d!='0'}
  if any(i<3 or c==81 for i,c in fixed.items()):return None
  return fixed
 covers=[]
 for (K,fc),vals in groups.items():
  fix=decode(K)
  if fix is None or collections.Counter(fix.values())+collections.Counter(fc)!=collections.Counter(far):continue
  un=[(fn,m) for fn,m in vals if m['domain']=='unordered']
  if un:
   fn,m=min(un,key=lambda x:x[1]['qmin']);covers.append((fix,m['qmin'],{fn}))
  ordered=[]
  for od in sorted(set(itertools.permutations(fc))):
   matches=[(fn,m) for fn,m in vals if m['domain']=='ordered' and tuple(m['coefs'])==od]
   if not matches:break
   ordered.append(min(matches,key=lambda x:x[1]['qmin']))
  else:covers.append((fix,max(m['qmin'] for fn,m in ordered),{fn for fn,m in ordered}))
 holes=[];used=set()
 for K,free,floor,fixed in need:
  maxfloor=max(maxfloor,floor);ef=decode(K);assert ef is not None
  for cf,qmin,files in covers:
   if any(ef.get(p)!=c for p,c in cf.items()):continue
   rem=[p for p in ef if p not in cf]
   if any(p<qmin for p in rem):continue
   if free and floor<qmin:continue
   if not free and max(floor,max(ef,default=-1)+1)<qmin:continue
   used.update(files);break
  else:holes.append([K,list(free),floor,list(fixed)])
 assert not holes,(key,holes)
 report[key]={'independent_slice_count':len(need),'files':sorted(used),'slice_cover_ok':True,'every_ordering':True,'initial_domain_only':len(need)==1 and all(K==K0 and tuple(free)==far and floor==3 for K,free,floor,fixed in need)}
finite=ROOT/'verification/indep2/e_brute_600.json'
out={'label':'COMPUTED','independent_enumerator':str(p.relative_to(ROOT)),'source_sha256':hashlib.sha256(p.read_bytes()).hexdigest(),'closed_configurations':report,'max_independent_slice_floor':maxfloor,'no_finite_exception_for_closed':all(v['initial_domain_only'] for v in report.values()),'finite_region':'Existing E lattice enumeration through 600 digits; hashed for context, not rerun','finite_region_sha256':hashlib.sha256(finite.read_bytes()).hexdigest()}
assert maxfloor<=600
json.dump(out,open(HERE/'independent_coverage.json','w'),indent=1)
print('INDEPENDENT COVER PASS',len(report),'configurations, max floor',maxfloor)
