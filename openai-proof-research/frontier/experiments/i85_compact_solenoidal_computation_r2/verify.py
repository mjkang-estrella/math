"""Offline, read-only I85 verifier. Evidence integrity/replay is not mathematical acceptance."""
from pathlib import Path
import sys,json,hashlib,re,subprocess,collections,concurrent.futures
from urllib.parse import unquote
sys.dont_write_bytecode=True
R=Path(__file__).resolve().parents[3];S=R/'frontier/sources/i85_compact_solenoidal_computation_r2';E=Path(__file__).parent
REPORT=R/'frontier/reviews/i85-compact-solenoidal-computation-r2.md'
PIN='fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb'
checks=[]
def sha(b):return hashlib.sha256(b).hexdigest()
def blob(b):return hashlib.sha1(b'blob '+str(len(b)).encode()+b'\0'+b).hexdigest()
def read(p):return json.loads(Path(p).read_text())
def check(ok,msg):
 if not ok:raise AssertionError(msg)
def verify_ref(x):
 b=(R/x['path']).read_bytes();check(sha(b)==x['sha256'],'hash '+x['path'])
 if 'bytes' in x:check(len(b)==x['bytes'],'size '+x['path'])
 return b
def add(name,result):checks.append(dict(check=name,result=result))
def owned():
 return {str(p.relative_to(R)) for d in (S,E) for p in d.rglob('*') if p.is_file() and p!=S/'seal-v1.json'}|{str(REPORT.relative_to(R))}
def main():
 if '--preseal' not in sys.argv:
  seal=read(S/'seal-v1.json');check(set(x['path'] for x in seal['files'])==owned(),'complete owned inventory')
  for x in seal['files']:verify_ref(x)
  add('owned immutable domain',dict(files=len(seal['files']),seal_sha256=sha((S/'seal-v1.json').read_bytes())))
 else:check(not (S/'seal-v1.json').exists(),'preseal only before first seal');add('owned domain','PRESEAL; not yet sealed')
 refs=read(S/'immutable-references.json')
 for x in refs:verify_ref(x)
 info=[];allowed={'README.md','frontier/README.md','frontier/TEN-FINDINGS.md','frontier/iterations/README.md'}
 for x in read(S/'inputs.json'):
  b=verify_ref(x);live=(R/x['live_path']).read_bytes()
  check(x['mutable']==(x['live_path'] in allowed),'mutable whitelist')
  if not x['mutable']:check(b==live,'immutable live input '+x['live_path'])
  else:info.append(dict(path=x['live_path'],informational_drift=live!=b,current_sha256=sha(live)))
 brief=read(R/'frontier/iterations/iteration85-compact-solenoidal-computation-r2-task.json')['brief']
 check(brief==(S/'full-brief.txt').read_text(),'complete assignment retention')
 supplied_author=brief.split('COMPLETE I80 AUTHOR REPORT:\n',1)[1].split('\nFINALIZED PARENT WRAPPER:',1)[0].strip()
 check(supplied_author==(R/'frontier/iterations/i80-geometric-flows-computation-discovery.md').read_text().strip(),'supplied original author identity')
 supplied_wrapper=json.loads(brief.split('FINALIZED PARENT WRAPPER:',1)[1].strip())
 check(supplied_wrapper==read(R/'frontier/experiments/i80-parent-verification.json'),'finalized supplied parent wrapper identity')
 author=read(R/'frontier/sources/i80_geometric_flows_computation_discovery/seal-v1.json')
 check(sha((R/'frontier/sources/i80_geometric_flows_computation_discovery/seal-v1.json').read_bytes())=='a3dddc3bf6f8065ed374df3ba288a817f680bd090f07d1343c695185617f04bc','original I80 seal')
 for x in author['files']:verify_ref(x)
 add('inputs and original author evidence',dict(immutable_references=len(refs),author_sealed_files=len(author['files']),mutable_information=info))
 tree=read(R/'sources/preprints-tree.json');check(not tree['truncated'] and len(tree['tree'])==13223,'full tree')
 blobs={x['path']:x for x in tree['tree'] if x['type']=='blob'};check(len(blobs)==10373,'blob count')
 check(len({p.split('/')[1] for p in blobs})==749,'manuscript count')
 d=read(R/'frontier/sources/i79_logarithmic_girth_spectra_novelty_r3/search-domain.json')
 check(len(d)==len({x['path'] for x in d})==10373 and {x['path'] for x in d}==set(blobs),'full search domain multiset')
 outside=[json.loads(l) for l in (R/'frontier/sources/i79_logarithmic_girth_spectra_novelty_r3/outside-requests.jsonl').read_text().splitlines()]
 ob={x['path']:x for x in outside};check(len(outside)==len(ob)==1033,'outside multiset')
 pdfpairs=[]
 for x in outside:
  b=(R/x['local']).read_bytes();check(sha(b)==x['sha256'] and blob(b)==blobs[x['path']]['sha']==x['sha'],'outside original bytes '+x['path'])
  check(x['status']==200 and x['git_match'] and len(b)==x['bytes']==x['size'],'outside response '+x['path'])
  check(unquote(x['url'])=='https://raw.githubusercontent.com/openai/math/'+PIN+'/'+x['path'],'outside URL')
  if 'extraction' in x:
   y=x['extraction'];check(y['code']==0 and sha((R/y['path']).read_bytes())==y['sha256'],'outside extraction binding');pdfpairs.append((R/x['local'],R/y['path']))
 searches=read(S/'searches.json');patterns=[re.compile(x['pattern']) for x in searches];hits=[[] for _ in searches]
 corpuspaths=[]
 for x in d:
  b=(R/x['local']).read_bytes();check(sha(b)==x['sha256'],'search body hash '+x['path'])
  if x['kind']=='corpus':
   check(x['path'] not in ob and blob(b)==blobs[x['path']]['sha'],'corpus Git identity');corpuspaths.append(x['local'])
  else:
   q=ob[x['path']];check(x['local']==q.get('extraction',{}).get('path',q['local']),'outside actual-body mapping')
  for i,line in enumerate(b.decode('utf8','replace').splitlines(),1):
   for j,pattern in enumerate(patterns):
    if pattern.search(line):hits[j].append([x['path'],i,line,x['kind']])
 actual={str(p.relative_to(R)) for p in (R/'frontier/sources/i14_spectral_width_novelty_r3/corpus').rglob('*') if p.is_file()}
 check(len(corpuspaths)==9340 and actual==set(corpuspaths),'all corpus files no ignored omissions')
 for x,h in zip(searches,hits):check(collections.Counter(map(tuple,x['hits']))==collections.Counter(map(tuple,h)),'exact search multiset '+x['name'])
 add('complete pinned body domain and searches',dict(blobs=10373,manuscripts=749,corpus=9340,outside=1033,pdf_bodies=len(pdfpairs),other_outside_bytes=1033-len(pdfpairs),searches=[dict(name=x['name'],hits=len(h)) for x,h in zip(searches,hits)]))
 # Re-extract all outside PDFs to stdout, without scratch files or network.
 def replay(pair):
  p,t=pair;o=subprocess.run(['pdftotext','-layout',str(p),'-'],capture_output=True)
  check(o.returncode==0 and o.stdout==t.read_bytes(),'PDF extraction replay '+str(p));return 1
 with concurrent.futures.ThreadPoolExecutor(max_workers=8) as pool:count=sum(pool.map(replay,pdfpairs))
 add('all outside PDF re-extractions',count)
 m=read(S/'source-manifest.json')
 for x in m:
  b=verify_ref(x);check(blob(b)==x['git_blob']==blobs[x['upstream_path']]['sha'],'selected Git identity');check(x['raw_url']=='https://raw.githubusercontent.com/openai/math/'+PIN+'/'+x['upstream_path'],'selected raw URL')
 allpass=[]
 for name in ['passages.json','primary-passages.json','compiled-passages.json']:
  ps=read(S/name);allpass+=ps
  for p in ps:
   b=verify_ref(p);lines=b.splitlines(keepends=True);check(1<=p['start']<=p['end']<=len(lines),'passage range')
   check(sha(b''.join(lines[p['start']-1:p['end']]))==p['passage_sha256'],'passage digest '+p['path'])
 coverage=read(S/'read-coverage.json')
 for x in coverage['files']:
  ps=[p for p in read(S/'passages.json') if p['path']==x['path']];covered=set()
  for p in ps:covered.update(range(p['start'],p['end']+1))
  check(len(covered)==x['read_lines'],'coverage count')
  unread={i for a,b in x['unread_ranges'] for i in range(a,b+1)};check(covered.isdisjoint(unread) and covered|unread==set(range(1,x['lines']+1)),'candid coverage partition')
 for v in read(S/'ib-versions.json'):
  a=(R/v['old']).read_bytes();b=(R/v['new']).read_bytes();check(sha(a)==v['old_sha256'] and sha(b)==v['new_sha256'] and (a==b)==v['identical'],'version relation')
 add('source contracts, passages and candid coverage',dict(selected_files=len(m),passages=len(allpass),canonical_full_fluid_bodies=['RV','ES','VD','SP','GS','FS','FP'],IB_PI='Scoped relevant contracts and proofs; unused alternative symbolic/routing bodies explicitly unbound',version_comparisons=len(read(S/'ib-versions.json'))))
 # Retained original primary response metadata/bytes, including failures.
 A=R/'frontier/sources/i80_geometric_flows_computation_discovery';responses=read(A/'primary-requests.json')+read(A/'primary-more-requests.json');np=0
 for x in responses:
  b=verify_ref(x)
  if x['path'].endswith('.pdf'):
   p=R/x['path'];t=p.with_suffix('.txt')
   if t.exists():replay((p,t));np+=1
 add('primary versions and retained responses',dict(responses=len(responses),PDF_replays=np,version_records=len(read(A/'primary-versions.json')),external_proof_premises=0))
 o=subprocess.run([sys.executable,'-B',str(E/'diagnostics.py')],capture_output=True,cwd=R)
 check(o.returncode==0,'independent diagnostics failed '+o.stderr.decode());check(o.stdout==(E/'diagnostics.json').read_bytes(),'exact independent diagnostic stdout')
 add('independent diagnostic replay',json.loads(o.stdout))
 scope=read(S/'scope.json');check(scope['nomination']=='HELD' and scope['accepted_count_increment']==0 and scope['broad_i80_assignment']=='NOT FULLY DISCHARGED','scope')
 add('mathematical and contribution scope',scope)
 return dict(status='PASS_EVIDENCE_ONLY',mode='preseal_read_only' if '--preseal' in sys.argv else 'sealed_read_only',checks=checks,failures=[],warning='Evidence replay is not a mathematical proof, novelty judgment, contribution acceptance, or full original I80 assignment discharge.')
try:
 result=main();print(json.dumps(result,indent=2,ensure_ascii=False))
except Exception as exc:
 print(json.dumps(dict(status='FAIL_EVIDENCE',checks=checks,failures=[str(exc)]),indent=2));sys.exit(1)
