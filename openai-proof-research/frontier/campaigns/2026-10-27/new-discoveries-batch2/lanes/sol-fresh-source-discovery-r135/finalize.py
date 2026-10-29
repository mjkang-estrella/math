import json,hashlib,datetime,sys
from pathlib import Path
L=Path(__file__).resolve().parent;B=L.parent.parent;R=L.parents[5]
def sha(b):return hashlib.sha256(b).hexdigest()
def dump(p,x):(L/p).write_text(json.dumps(x,indent=2)+'\n')
if sys.argv[1]=='audit':
 j=json.loads((L/'check-results.json').read_text())
 print('stronger violations',[(x['n'],x['adj'],x['stronger_clique_cover_bridge']) for x in j['random_graphs'] if not all(x['stronger_clique_cover_bridge'].values())])
 print('controls',j['controls'])
 h=json.loads((L/'history-receipt.json').read_text());print('r111-r113 originals',len(h['retained_r111_r113']))
 print('registry matches',len(json.loads((L/'registry-retained.json').read_text())['hits']))
elif sys.argv[1]=='build':
 retained=[]
 for rel in ['sol-fresh-source-discovery-r101/sources/survey-current.pdf','sol-fresh-source-discovery-r101/sources/survey-current.txt','sol-fresh-source-discovery-r101/sources/survey-current-abs.html','sol-fresh-source-discovery-r101/http.json','sol-fresh-source-discovery-r101/discovery.md','sol-fresh-source-discovery-r66/discovery.md']:
  p=L.parent/rel
  if p.exists():
   b=p.read_bytes();name='retained-'+p.parent.parent.name+'-'+p.name if '/sources/' in rel else 'retained-'+p.parent.name+'-'+p.name
   (L/'sources'/name).write_bytes(b);retained.append(dict(original=str(p),copy='sources/'+name,bytes=len(b),sha256=sha(b),qualification='retained historical bytes; not a live retrieval'))
 context=[]
 for p in [R/'AGENTS.md',B/'AGENTS.md',B/'ledger.json',B/'prior-campaign-context.json',B/'NEXT.md',L.parent/'root-r131-r132-handback/DECISION.md',L.parent/'root-r133-handback/DECISION.md']:
  b=p.read_bytes();name='context-'+str(len(context))+p.suffix;(L/'sources'/name).write_bytes(b);context.append(dict(original=str(p),copy='sources/'+name,sha256=sha(b),mutable=p.name=='NEXT.md'))
 dump('context-final-receipts.json',context)
 inherited=[]
 for lane,name in [('sol-fresh-source-discovery-r133','registry-delta-receipt.json'),('sol-fresh-source-discovery-r130','registry-delta-receipt.json'),('sol-fresh-source-discovery-r129','registry-delta-receipt.json'),('sol-fresh-source-discovery-r125','registry-delta-receipt.json'),('sol-fresh-source-discovery-r119','registry-delta-receipt.json'),('sol-renyi-registry-gap-closure-r3','semantic-read-receipts.json')]:
  p=L.parent/lane/name
  if p.exists():
   b=p.read_bytes();json.loads(b);inherited.append(dict(path=str(p),sha256=sha(b),bytes=len(b),scope='historical metadata only; no target semantic clearance'))
 g=L.parent/'sol-edge-irregulator-manuscript-packet-r1/packet/helper_guard.py'
 dump('provenance.json',dict(status='UNRESOLVED_NO_NOMINEE',credit_requested=0,utc=datetime.datetime.now(datetime.timezone.utc).isoformat(),counts_inherited=dict(additional=9,total=39,next=40),primary_retrievals=[json.loads(x) for x in (L/'http.jsonl').read_text().splitlines()],retained_primary_and_dispositions=retained,context='context-final-receipts.json',historical_reports='history-receipt.json',registry_index='registry-retained.json',registry_delta='registry-delta.json',inherited_receipts=inherited,guard=dict(path=str(g),sha256=sha(g.read_bytes()),AS=512*1024*1024,group_RSS=512*1024*1024,CPU=210,wall=230,sample_ms=40,BLAS=1),limits=['Report-role history only; not all original source bodies.','Retained tree/path registry index is lexical, incomplete semantic coverage.','Full fixed compare interval within caps, no all-body semantic clearance.','Journal403 and source-version distinction preserved.','25 sampled graphs, 3 controls and216 constructions are diagnostics only.','No source theorem, source counterexample, Lean, manuscript or count change.'],failures=['Initial combined reads and one-line JSON native grep truncated displays.','Web author-hosted PDF fetch timeout; primary institutional copy obtained.','Guessed successorv2 returned404; actual latestv1 retrieved.','ORO403 no retry or bypass.','Successor pdftotext font warning.','First discovery patch malformed and rejected without partial write.'],external_mutations=False,git=False,children=False))
 # Context remains separate from scientific evidence; only local copies are sealed.
 sci={}
 for p in sorted(L.rglob('*')):
  if not p.is_file() or p.name in ['finalmanifest.json','scientific-freeze.json','manifest-verification.json']:continue
  rel=str(p.relative_to(L))
  if p.name.startswith('context-') or rel.startswith('sources/context-'):continue
  sci[rel]=sha(p.read_bytes())
 dump('scientific-freeze.json',sci)
 files={str(p.relative_to(L)):dict(sha256=sha(p.read_bytes()),bytes=p.stat().st_size) for p in sorted(L.rglob('*')) if p.is_file() and p.name not in ['finalmanifest.json','manifest-verification.json']}
 dump('finalmanifest.json',dict(files=files,scope='all lane files at seal time except self and subsequent verification receipt'))
 print('sealed',len(files),'science',len(sci))
elif sys.argv[1]=='verify':
 j=json.loads((L/'finalmanifest.json').read_text());errors=[]
 for p,r in j['files'].items():
  b=(L/p).read_bytes()
  if len(b)!=r['bytes'] or sha(b)!=r['sha256']:errors.append(p)
 dump('manifest-verification.json',dict(entries=len(j['files']),errors=errors,passed=not errors))
 print('manifest',len(j['files']),'errors',errors)
 if errors:sys.exit(1)
