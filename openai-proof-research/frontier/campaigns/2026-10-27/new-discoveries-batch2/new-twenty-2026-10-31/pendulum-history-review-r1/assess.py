import os,resource,signal,json,hashlib,datetime,urllib.request,urllib.error,re
from pathlib import Path
os.sched_setaffinity(0,sorted(os.sched_getaffinity(0))[:2]);resource.setrlimit(resource.RLIMIT_AS,(768*2**20,768*2**20));resource.setrlimit(resource.RLIMIT_CPU,(120,120));signal.alarm(180)
B=Path('/home/mj-kang/Documents/Dev/math/openai-proof-research/frontier/campaigns/2026-10-27/new-discoveries-batch2');L=B/'new-twenty-2026-10-31/pendulum-history-review-r1'; tracked={};receipts=[]
def read(p):
 p=Path(p);d=p.read_bytes();tracked[str(p)]={'sha256':hashlib.sha256(d).hexdigest(),'bytes':len(d)};return d.decode(errors='replace')
def js(p):return json.loads(read(p))
def save(n,x):(L/n).write_text(json.dumps(x,indent=2,ensure_ascii=False))
def fetch(n,url):
 t=datetime.datetime.now(datetime.timezone.utc).isoformat();r={'utc':t,'url':url}
 try:
  with urllib.request.urlopen(urllib.request.Request(url,headers={'User-Agent':'Math source review (read-only)'}),timeout=20) as f:d=f.read(8*2**20);r.update(status=f.status,final_url=f.url)
 except urllib.error.HTTPError as e:d=e.read();r.update(status=e.code)
 except Exception as e:receipts.append(dict(r,error=str(e)));return None
 (L/n).write_bytes(d);r.update(path=str(L/n),sha256=hashlib.sha256(d).hexdigest(),bytes=len(d));receipts.append(r);print(n,r['status'],len(d),flush=True)
 return json.loads(d) if r['status']==200 else None
head=fetch('live-openai-head.json','https://api.github.com/repos/OpenAI/math/commits/main')
omega=fetch('live-omega-head.json','https://api.github.com/repos/the-omega-institute/trureturing/commits/main')
aim=fetch('live-aim-head.json','https://api.github.com/repos/MColbrook/AIM/commits/main')
citers=fetch('live-citers.json','https://api.openalex.org/works?filter=cites:W3097405001&per-page=50')
save('http-receipts.json',receipts)
# Actual 39 accepted scopes, aliases and source URLs, not only ID search.
first=js(B.parent/'2026-10-26/new-discoveries/ledger.json') if (B.parent/'2026-10-26/new-discoveries/ledger.json').exists() else js('/home/mj-kang/Documents/Dev/math/openai-proof-research/frontier/campaigns/2026-10-26/new-discoveries/ledger.json')
second=js(B/'ledger.json');context=js(B/'prior-campaign-context.json')
alias=re.compile(r'343384|1907\.13009|00851-9|pendulum|cholesteric|grinfeld|xayxanadasy|mottram|complementary.*moment|time.?map',re.I)
rows=[]
for ledger in [first,second]:
 for a in ledger['accepted']:rows.append({'number':a['number'],'title':a.get('title'),'scope':a.get('scope'), 'source_target':a.get('source_target'),'alias_hits':alias.findall(json.dumps(a))})
save('credit-family-comparison.json',rows);print('accepted scopes',len(rows),'alias hits',[a for a in rows if a['alias_hits']],flush=True)
# full inputs and actually relied-on reviews
for p in js(L/'frozen-inputs.json'):read(p)
for p in [L/'reservation.json',B/'AGENTS.md',B/'new-twenty-2026-10-31/AGENTS.md',Path('/home/mj-kang/Documents/Dev/math/openai-proof-research/AGENTS.md'),Path('/home/mj-kang/Documents/Dev/math/openai-proof-research/sources/upstream.json')]:read(p)
for lane,files in {'sol-steiner-gp-fixed-gap-closure-r3':['review.md','coverage.json','interval-commits.json','commit-file-coverage.json','diff-coverage.json'], 'sol-steiner-gp-offline-citation-closure-r4':['review.md','offlinecoverage.json','cache-inspection.json','tree-inventory.json'], 'root-steiner-gp-gap-hold-r3':['DECISION.md'], 'root-steiner-gp-parked-hold-r4':['DECISION.md'],'sol-pendulum-manuscript-packet-r1':['packet/paper/paper.txt']}.items():
 for f in files:read(B/'lanes'/lane/f)
# Targeted historical retained diff content; no reconstruction claim.
d=B/'lanes/sol-steiner-gp-fixed-gap-closure-r3';cov=js(d/'diff-coverage.json'); selected=[]; exact=[]
for c in cov:
 p=d/c['file'];s=read(p)
 for block in s.split('diff --git ')[1:]:
  path=block.splitlines()[0];hits=alias.findall(block)
  if hits:exact.append({'commit':c['commit'],'path':path,'hits':sorted(set(hits)),'block_sha256':hashlib.sha256(('diff --git '+block).encode()).hexdigest(),'excerpt':block[:18000]})
  if re.search(r'IncompleteBeta|EllipticTail|[Pp]endulum|[Tt]ime[Mm]ap|[Cc]holesteric',path):selected.append({'commit':c['commit'],'path':path,'block':block[:24000]})
save('historical-target-hits.json',exact);save('historical-topic-blocks.json',selected);print('historic exact/topic',len(exact),len(selected),flush=True)
# Current OpenAI omitted patches precisely enumerated, no content claimed from absent patches.
h=head or js(B/'new-twenty-2026-10-31/expanded-corpus-r35/sources/registry-head.response');missing=[{'path':f['filename'],'status':f['status'],'sha':f['sha']} for f in h.get('files',[]) if 'patch' not in f];save('openai-missing-patches.json',missing)
tree=js(B/'new-twenty-2026-10-31/fresh-corpus-r10/sources/registry-preprints.json');save('current-tree-target-screen.json',{'head':h.get('sha'),'tree':tree['sha'],'truncated':tree['truncated'],'entries':len(tree['tree']),'exact_path_hits':[a for a in tree['tree'] if alias.search(a['path'])], 'limits':'Complete current preprints inventory only; not deleted historical content or complete lean tree.'})
# inherited actual primary and selected registry bodies hash-only references
p=B/'lanes/sol-pendulum-source-subsumption-review-r2/research'
for f in ['cholesteric.txt','schaaf-definitions.txt','schaaf-pages-39.txt','smoller-D.txt','rivulets-appendix.txt','rivulets-sections.txt']:read(p/f)
p=B/'lanes/sol-pendulum-investment-review-r3/research';screen=js(p/'registry-topic-screen.json')
for a in screen['bodies']:read(p/a['file'])
for f in ['retrievals.json','supplement-screen.json']:read(p/f)
for f in ['registry-check.json','source-receipts.json']:read(B/'new-twenty-2026-10-31/expanded-corpus-r35'/f)
read(B/'new-twenty-2026-10-31/expanded-corpus-r33/registry-path-screen.json')
# exact repaired archive, without extracting or building
p=B/'lanes/root-pendulum-replay-context-fix-r2'
for f in p.glob('*.zip'):read(f)
print('archives',list(p.glob('*.zip')),flush=True)
save('additional-input-hashes.json',tracked)
print('DONE',len(tracked),flush=True)
