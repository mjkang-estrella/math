#!/usr/bin/env python3
"""Offline read-only I86 verifier. No network, writes, repair, or seal generation."""
import pathlib,json,hashlib,re,sys,subprocess,collections,concurrent.futures
R=pathlib.Path(__file__).resolve().parents[3];S=R/'frontier/sources/i86_compact_solenoidal_computation_novelty_r3';E=R/'frontier/experiments/i86_compact_solenoidal_computation_novelty_r3';REPORT=R/'frontier/reviews/i86-compact-solenoidal-computation-novelty-r3.md'
SEAL=S/'seal-v1.json';ANCHOR=S/'anchor.json'
def H(b):return hashlib.sha256(b).hexdigest()
def get(p):return json.loads(p.read_text())
def checkref(x,key='path'):
 b=(R/x[key]).read_bytes();assert H(b)==x['sha256'],x[key]
 if 'bytes'in x:assert len(b)==x['bytes'],x[key]
 return b
def inventory():return sorted([p for d in (S,E) for p in d.rglob('*') if p.is_file() and p not in (SEAL,ANCHOR)]+[REPORT])
def lf(b):
 a=b.decode().split('\n');return [x+'\n' for x in a[:-1]]+([a[-1]] if a[-1] else [])
def extract(args):
 p,expected=args;c=subprocess.run(['pdftotext','-layout',str(R/p),'-'],capture_output=True);assert c.returncode==0,(p,c.stderr.decode());assert H(c.stdout)==expected,p;return 1
checks=[]
def done(name,data):checks.append({'check':name,'result':data});print(name,file=sys.stderr,flush=True)
try:
 if SEAL.exists():
  seal=get(SEAL);assert sorted(x['path'] for x in seal['files'])==[str(p.relative_to(R)) for p in inventory()]
  for x in seal['files']:checkref(x)
  assert get(ANCHOR)['seal_sha256']==H(SEAL.read_bytes())
  done('exact immutable owned domain',{'files':len(seal['files']),'seal_sha256':H(SEAL.read_bytes())})
 else:
  assert '--preseal' in sys.argv,'missing seal'
  done('preseal inventory',len(inventory()))
 refs=get(S/'immutable-refs.json')
 for x in refs:checkref(x)
 for p,key in [('frontier/sources/i80_geometric_flows_computation_discovery/seal-v1.json','files'),('frontier/sources/i79_logarithmic_girth_spectra_novelty_r3/seal-v1.json','artifacts')]:
  old=get(R/p)
  for x in old[key]:checkref(x)
 led=[]
 for x in get(S/'ledgers.json'):
  assert H((R/x['snapshot']).read_bytes())==x['sha256']
  led.append({'path':x['live'],'informational_drift':H((R/x['live']).read_bytes())!=x['sha256']})
 done('immutable old references and four fixed ledger snapshots',{'refs':len(refs),'live_ledgers':led})
 tree=get(R/'sources/preprints-tree.json');assert not tree['truncated'];blobs={x['path']:x for x in tree['tree'] if x['type']=='blob'}
 domain=get(S/'search-domain.json');assert len(domain)==len(blobs)==10373 and {x['path'] for x in domain}==set(blobs)
 assert len(tree['tree'])==13223 and len({x['path'].split('/')[1] for x in domain})==749
 outside=get(S/'outside-raw-refs.json');raw={x['path']:x for x in outside};assert len(raw)==1033
 bodies=[];pdfs=[]
 for x in domain:
  b=(R/x['local']).read_bytes();assert H(b)==x['sha256'],x['local'];bodies.append((x['path'],b))
  if x['kind']=='corpus':original=b
  else:
   z=raw[x['path']];original=checkref(z,'local');assert z['git_blob']==blobs[x['path']]['sha']
   if x['kind']=='outside_pdf':
    assert z['extraction']['sha256']==x['sha256'] and z['extraction']['path']==x['local'];pdfs.append((z['local'],x['sha256']))
  assert hashlib.sha1(b'blob '+str(len(original)).encode()+b'\0'+original).hexdigest()==blobs[x['path']]['sha'],x['path']
 done('all actual pinned representatives and raw outside blobs',dict(collections.Counter(x['kind'] for x in domain)))
 with concurrent.futures.ThreadPoolExecutor(max_workers=6) as ex:n=sum(ex.map(extract,pdfs))
 done('all outside PDF extraction replay',n)
 for name,spec in get(S/'searches.json').items():
  rg=re.compile(spec['pattern'],re.I);hits=[[p,i,l] for p,b in bodies for i,l in enumerate(b.decode('utf8','replace').splitlines(),1) if rg.search(l)]
  assert hits==get(S/('search-'+name+'.json'));assert len(hits)==spec['hits'];assert len({x[0] for x in hits})==spec['files']
 done('full-domain ordered search multisets',{k:{z:v[z] for z in ['hits','files']} for k,v in get(S/'searches.json').items()})
 m=get(S/'fluid-manifest.json');queue=get(S/'read-queue.json');covered=collections.defaultdict(set)
 for x in m:
  b=checkref(x);assert x['git_blob']==blobs[x['upstream_path']]['sha'];assert x['raw_url']=='https://raw.githubusercontent.com/openai/math/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/'+x['upstream_path']
 for x in get(S/'reads.json')+get(S/'extra-reads.json'):
  b=checkref(x);ls=b.decode().splitlines(keepends=True);assert H(''.join(ls[x['start']-1:x['end']]).encode())==x['passage_sha256'];covered[x['sha256']].update(range(x['start'],x['end']+1))
 for x in queue:assert set(range(1,len((R/x['path']).read_text().splitlines())+1))<=covered[x['sha256']]
 coverage=get(S/'read-coverage.json');assert coverage['distinct_lines']==18965 and len(queue)==77 and len(m)==91
 families={x['upstream_path'].split('/')[1] for x in m};assert len(families)==10
 assert {x['upstream_path'] for x in m}=={x['path'] for x in domain if x['path'].split('/')[1] in families and x['kind']!='outside_pdf'}
 union=sorted({tuple(x) for name in get(S/'searches.json') for x in get(S/('search-'+name+'.json')) if x[0].split('/')[1] not in families})
 assert [list(x) for x in union]==get(S/'off-family-matches.json')
 cls=get(S/'off-family-classification.json');assert sorted(i for x in cls['groups'] for i in x['hit_indices'])==list(range(len(union)))
 done('full scoped fluid read bindings and off-family match audit',{'distinct_lines':18965,'distinct_bodies':77,'physical_files':91,'off_family_passages':len(union)})
 http=[]
 for f in ['primary-responses.json','primary-supplement-responses.json','primary-routing-responses.json','primary-almost-responses.json']:http+=get(S/f)
 conversions=[]
 for x in http:
  if 'path' not in x:assert 'error'in x;continue
  b=checkref(x);assert all(k in x for k in ['url','final_url','started','finished','status','headers'])
  if 'conversion'in x:
   c=x['conversion'];assert H((R/c['text']).read_bytes())==c['sha256'];conversions.append((x['path'],c['sha256']))
 with concurrent.futures.ThreadPoolExecutor(max_workers=4) as ex:n=sum(ex.map(extract,conversions))
 for x in get(S/'primary-reads.json'):
  b=checkref(x);ls=lf(b);assert len(ls)==x['lines']
  for z in x['ranges']:assert H(''.join(ls[z['start']-1:z['end']]).encode())==z['passage_sha256']
 for x in get(S/'version-comparisons.json'):assert checkref(x['old'])==checkref(x['current']) and x['text_identical']
 done('primary response, extraction, version and actual passage bindings',{'responses':len(http),'extractions':n,'read_bodies':len(get(S/'primary-reads.json')),'status_counts':dict(collections.Counter(x.get('status','error') for x in http))})
 c=subprocess.run([sys.executable,'-B',str(E/'diagnostics.py')],capture_output=True);assert c.returncode==0,c.stderr.decode();assert c.stdout==(S/'diagnostics.json').read_bytes()
 done('independent finite diagnostic replay',json.loads(c.stdout))
 status=get(S/'status.json');assert status['significance']=='TECHNICAL' and status['accepted_increment']==0 and status['original_proof']=='I85_PENDING_NOT_READ_OR_BOUND'
 done('separate proof/contribution/evidence scope',status)
 print(json.dumps({'status':'PASS_EVIDENCE_ONLY','mode':'sealed_read_only' if SEAL.exists() else 'preseal_read_only','checks':checks,'warning':'Not original-proof PASS, worldwide priority, or finding acceptance.'},indent=2))
except Exception as e:
 print(json.dumps({'status':'FAIL_EVIDENCE','checks':checks,'failure':repr(e)},indent=2));raise
