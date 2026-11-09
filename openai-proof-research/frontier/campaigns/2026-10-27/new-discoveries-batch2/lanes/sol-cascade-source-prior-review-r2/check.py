"""Offline exact evidence replay. No network, formal work, or candidate writes."""
import os
for k in ('OPENBLAS_NUM_THREADS','OMP_NUM_THREADS','MKL_NUM_THREADS','NUMEXPR_NUM_THREADS'):os.environ[k]='1'
import resource
resource.setrlimit(resource.RLIMIT_AS,(536870912,536870912))
resource.setrlimit(resource.RLIMIT_CPU,(25,25))
import json,hashlib,re,datetime
from pathlib import Path
b=Path(__file__).resolve().parent; campaign=b.parent.parent
p=b.parent/'sol-cascade-rate-preliminary-review-r1'
def sha(f):return hashlib.sha256(f.read_bytes()).hexdigest()
def load(f):return json.loads(f.read_text())
terms=load(b/'registry-screen.json')['terms']
checks={};frozen={}
for lane in ('root-cascade-rate-candidate-r1','root-log-arctangent-candidate-r1'):
 c=b.parent/lane;manifest=load(c/'review-freeze.json')['hashes']
 assert all(sha(c/k)==h for k,h in manifest.items())
 frozen[lane]={'files':len(manifest),'all_match':True,'freeze_manifest_sha256':sha(c/'review-freeze.json')}
ledger=load(campaign/'ledger.json');assert (ledger['accepted_count'],ledger['total_accepted_count'])==(3,33)
base=load(p/'sources/omega-head');root=load(p/'sources/omega-root.json');assert root['sha']==base['commit']['tree']['sha']
expected={'D5':('daacae648bfa8745c6b1604b3988ee2b7ff95d8170b53fdb7916c1861342ff53',12445),'Problems':('b605d0658347555f9cd50487db2e566c68a23a8af2fbcf048ed6d95634eb3ed3',1538)}
for name,(h,n) in expected.items():
 f=p/f'sources/omega-{name}.json';j=load(f)
 assert sha(f)==h and j['truncated'] is False and len(j['tree'])==n
 assert j['sha']==next(e['sha'] for e in root['tree'] if e['path']==name)
 assert len({e['path'] for e in j['tree']})==n
 checks[name]={'sha256':h,'entries':n,'truncated':False,'all_matches':{g:[e['path'] for e in j['tree'] if any(t.lower() in e['path'].lower() for t in ts)] for g,ts in terms.items()}}
heads={}
for name in ('omega','openai','count'):
 ids=set(re.findall(r'"currentOid":"([a-f0-9]{40})"',(b/f'sources/{name}-page.html').read_text()));assert len(ids)==1;heads[name]=ids.pop()
assert heads['openai']=='7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a'
assert heads['count']=='dbf673741a54c7dc9d88a6aec0e8148a538f4a3a'
r7=b.parent/'sol-fresh-analysis-discovery-r7/sources';others=[]
for name,h in [('openai-preprints-tree.json','6ac178a0ebcece8f2c2c9aa1c22022068110bbdae4bb3d1ffa9f1b693b9e0305'),('current-CONTENTS.md','080badcb677fb80be0e695c21a8ec88bcb3a46dd3e3078ca10061e6b289be175'),('count-registry.json','542ac19db32bba79aa5b86df0438c94779310cdabf441f1b18a6b0f166f23687')]:
 f=r7/name;assert sha(f)==h;s=f.read_text();j=load(f) if name.endswith('.json') else None
 if isinstance(j,dict) and 'truncated' in j:assert j['truncated'] is False
 others.append({'file':str(f),'sha256':h,'matches':{g:[t for t in ts if t.lower() in s.lower()] for g,ts in terms.items()}})
delta=(b/'sources/omega-delta.diff').read_text();patch=(b/'sources/omega-delta.patch').read_text()
paths=sorted(set(re.findall(r'^diff --git a/(.*?) b/',delta,re.M)))
commits=re.findall(r'^From ([a-f0-9]{40}) ',patch,re.M)
assert len(commits)==38 and '[PATCH 38/38]' in patch and len(paths)>0
assert not any(x in delta.lower() for x in ['diff truncated','diff too large','captcha','incapsula'])
# Keywords are screened over entire net diff as well as every changed path.
delta_hits={g:[t for t in ts if t.lower() in delta.lower()] for g,ts in terms.items()}
# Exact supplementary PDF identity: archived publication URL + title, source filename, dates.
assert sha(b/'sources/supplement-2021.pdf')=='d691c3a9935abf9e8a11f2cdfe09ed70cf28e287c6a739ba86a4a6283a06aa7e'
assert (b/'sources/supplement-2021.pdf').read_bytes().startswith(b'%PDF-')
# Minimal exact recurrence/inequality check; general proof is in review.md.
n=0;bounds=0
for k in range(1,201):
 prev=n;n=k*k*(prev+k+10)
 if k<3:continue
 H=prev+3;R=n-2*k-2-H;B,r=divmod(R,k);D=n-1-(k-2)*B
 assert R>=0 and 0<=D and k*D<=2*n+k*prev+k*(3*k+5)
 bounds+=1
out={'utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'status':'PASS: exact evidence only, not formal proof','frozen':frozen,'counts':[3,33],'base_head':base['sha'],'current_heads_observed':heads,'complete_base_trees':checks,'other_registry_evidence':others,'new_head_comparison':{'paths':paths,'path_count':len(paths),'patch_commits':len(commits),'whole_diff_hits':delta_hits,'sha256':sha(b/'sources/omega-delta.diff'),'limitation':'Complete base trees plus public comparison response; no new recursive-tree SHA claimed.'},'exact_bound_instances':bounds}
(b/'checks.json').write_text(json.dumps(out,indent=2));print(json.dumps({k:out[k] for k in ('status','frozen','counts','current_heads_observed','exact_bound_instances')},indent=2))
