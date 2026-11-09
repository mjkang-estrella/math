import os,resource
os.sched_setaffinity(0,sorted(os.sched_getaffinity(0))[:2]);resource.setrlimit(resource.RLIMIT_CPU,(120,120));resource.setrlimit(resource.RLIMIT_AS,(6*1024**3,6*1024**3))
import sys,pathlib,json,time,re,html
sys.path.insert(0,str(pathlib.Path(__file__).resolve().parent));import review_ops as r
for n in ['provenance.json','results.json']:
 j=json.loads(r.read(r.BASE/n));print(n,'keys',list(j)[:30]);print(json.dumps({k:j[k] for k in ['381265','331096'] if k in j},indent=2))
for n in ['read-inventory.json','observed-exits.json','sources/selected-source-inventory.json','receipts/focused-reading.json','receipts/handback.json','sources/registry-openai-heads.json','sources/registry-tau-heads.json','sources/registry-pool-heads.json']:
 p=r.BASE/n
 if p.exists():
  j=json.loads(r.read(p));print(n, 'structure',list(j)[:15] if isinstance(j,dict) else len(j));
  if 'inventory' not in n:print(json.dumps(j)[:9000])
p=r.LANE/'live/ideal-operations.lean';s=r.read(p).decode().splitlines()
for i,l in enumerate(s):
 if re.search('theorem radical_inf|theorem.*inf_le|lemma.*inf_le|comap_radical|radical_le',l):print('\n'.join(s[max(0,i-3):i+12]))
s=r.read(r.LANE/'live/wu-cv.html').decode();s=html.unescape(re.sub('<[^>]*>',' ',s));i=s.lower().find('directed cycles');print('CV excerpt',s[i-120:i+200])
print(r.read(r.LANE.parent/'expanded-corpus-r372-parent-integration.json').decode())
r.finish('summary-'+str(time.time_ns()))
