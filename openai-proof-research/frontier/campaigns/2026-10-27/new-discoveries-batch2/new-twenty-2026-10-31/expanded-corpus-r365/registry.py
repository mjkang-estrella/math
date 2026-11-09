import os,resource
os.sched_setaffinity(0,sorted(os.sched_getaffinity(0))[:2]);resource.setrlimit(resource.RLIMIT_CPU,(120,120));resource.setrlimit(resource.RLIMIT_AS,(6*1024**3,6*1024**3))
import pathlib,sys,runpy,urllib.request,datetime,re,json,concurrent.futures
sys.argv.append('registry');g=runpy.run_path(str(pathlib.Path(__file__).with_name('research.py')));L=g['L'];js=g['js'];write=g['write'];sha=g['sha']
items=[('openai-head','https://github.com/openai/math'),('leanpool-head','https://github.com/LeanPool/lean-pool'),('tauceti-head','https://github.com/TauCetiProject/TauCeti'),('openai-current','https://raw.githubusercontent.com/openai/math/main/lean/formalization.yaml'),('openai-pinned','https://raw.githubusercontent.com/openai/math/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/lean/formalization.yaml'),('leanpool-import','https://raw.githubusercontent.com/LeanPool/lean-pool/main/LeanPool.lean'),('tauceti-import','https://raw.githubusercontent.com/TauCetiProject/TauCeti/main/TauCeti.lean')]
def fetch(t):
 n,u=t;r={'name':n,'url':u,'utc':datetime.datetime.now(datetime.timezone.utc).isoformat()}
 try:
  with urllib.request.urlopen(u,timeout=15) as f:b=f.read(5000000);r.update(status=f.status,finalURL=f.url,bytes=len(b),sha256=sha(b))
  write('registry/'+n+'.txt',b);s=b.decode(errors='replace');r['head_candidates']=list(dict.fromkeys(re.findall(r'"currentOid":"([0-9a-f]{40})"',s)));r['read_depth']='routing catalogue only; no absence clearance'
  if 'head' not in n:
   lines=s.splitlines();hits=[]
   for i,l in enumerate(lines,1):
    if any(t in l.lower() for t in ['crown','bunkbed']):continue
    if re.search('centrality|walkregular|walk.regular|jordan|frumious|metricdimension|metric.dimension|staged|hadamard|kahn|peeva|balog|supercyclic',l,re.I):hits.append([i,l])
   r['routing_hits']=hits
 except Exception as e:r.update(error=repr(e),status=getattr(e,'code',None))
 return r
with concurrent.futures.ThreadPoolExecutor(max_workers=2) as e:out=list(e.map(fetch,items))
js('http-registry.json',out)
for r in out:print(json.dumps(r))
P=L.parents[5]/'sources'
# actual source root fixed below; catalogue routing only
P=pathlib.Path('/home/mj-kang/Documents/Dev/math/openai-proof-research/sources')
s=(P/'CONTENTS.md').read_text();out=[]
for block in s.split('</tbody>'):
 if any(t in block.lower() for t in ['crown','transitive-bunkbed']):continue
 if re.search('centrality|walk.regular|frumious|metric dimension|staged tree|hadamard product|kahn|peeva|balog|super.cyclic',block,re.I):out.append(block)
write('pinned-catalogue-routing.txt','\n'.join(out));print('PINNED ROUTING', '\n'.join(out)[:7000])
