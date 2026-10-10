#!/usr/bin/env python3
"""I80 offline, read-only evidence verifier. PASS is neither proof nor novelty acceptance.

No fetching, file creation, mutation, seal creation, imports of development scripts,
or acceptance-count changes. --preseal omits only the as-yet nonexistent outer seal.
Requires Python 3, ripgrep, and pdftotext for exact retained extraction replay.
"""
from pathlib import Path
import argparse,hashlib,json,subprocess,sys,re,difflib,os
R=Path(__file__).resolve().parents[3]
S=R/'frontier/sources/i80_geometric_flows_computation_discovery'
E=R/'frontier/experiments/i80_geometric_flows_computation_discovery'
REPORT=R/'frontier/iterations/i80-geometric-flows-computation-discovery.md'
C=R/'frontier/sources/i14_spectral_width_novelty_r3/corpus'
PIN='fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb'
MUTABLE={'README.md','frontier/README.md','frontier/TEN-FINDINGS.md','frontier/iterations/README.md'}
SEAL=S/'seal-v1.json'
def sha(b):return hashlib.sha256(b).hexdigest()
def gitblob(b):return hashlib.sha1(b'blob '+str(len(b)).encode()+b'\0'+b).hexdigest()
def read(name):return json.loads((S/name).read_text())
def need(condition,msg):
 if not condition:raise AssertionError(msg)
def checkfile(path,expected):
 p=R/path;need(p.is_file(), 'missing '+path);b=p.read_bytes();need(sha(b)==expected,'hash drift '+path);return b
checks=[];failures=[]
def check(name,fn):
 try:checks.append({'check':name,'result':fn()})
 except Exception as exc:failures.append({'check':name,'error':type(exc).__name__+': '+str(exc)})
def assigned_files():
 return sorted([REPORT]+[p for d in [S,E] for p in d.rglob('*') if p.is_file() and p!=SEAL],key=lambda p:str(p.relative_to(R)))
def outer():
 data=read('seal-v1.json');need(data['pin']==PIN,'seal pin');files=assigned_files();need([str(p.relative_to(R)) for p in files]==[x['path'] for x in data['files']],'assigned inventory mismatch')
 for e in data['files']:
  b=checkfile(e['path'],e['sha256']);need(len(b)==e['bytes'],'assigned byte size')
 return {'files':len(files),'seal_sha256':sha(SEAL.read_bytes())}
def inputs():
 out=[];snapshots=read('inputs.json');need({x['path'] for x in snapshots if x['mutable']}==MUTABLE,'mutable exception set')
 for e in snapshots:
  b=checkfile(e['snapshot'],e['sha256']);actual=sha((R/e['path']).read_bytes());drift=actual!=e['sha256']
  if not e['mutable']:need(not drift,'immutable input drift '+e['path'])
  else:out.append(dict(path=e['path'],current_sha256=actual,informational_drift=drift))
 task=next(x for x in snapshots if x['path'].endswith('-task.json'))
 need((S/'full-brief.txt').read_text()==json.loads((R/task['snapshot']).read_text())['brief']+'\n','complete original brief')
 for e in read('immutable-references.json'):
  b=checkfile(e['path'],e['sha256']);need(len(b)==e['bytes'],'immutable reference bytes')
 return {'inputs':len(snapshots),'immutable_references':len(read('immutable-references.json')),'mutable_information':out}
def corpus():
 d=read('corpus-domain.json');tree=json.loads((R/'sources/preprints-tree.json').read_text())
 need(not tree.get('truncated',False),'tree truncated');entries=tree['tree'];blobs={e['path']:e for e in entries if e['type']=='blob'}
 need((len(entries),len(blobs),len({e['path'].split('/')[1] for e in entries}))==(13223,10373,749),'complete tree counts')
 got=subprocess.run(['rg','--files','--no-ignore',str(C)],stdout=subprocess.PIPE,stderr=subprocess.PIPE,check=True).stdout.decode().splitlines()
 need(sorted(str(Path(x).relative_to(R)) for x in got)==[e['path'] for e in d['files']],'fixed-domain exact file inventory')
 need(len(d['files'])==9340,'fixed text count')
 for e in d['files']:
  b=checkfile(e['path'],e['sha256']);need(len(b)==e['bytes'],'corpus byte size');need(gitblob(b)==e['git_blob']==blobs[e['upstream_path']]['sha'],'Git blob '+e['path'])
  need(e['path']==str(C.relative_to(R))+'/'+e['upstream_path'],'corpus path mapping')
 missing=sorted([e for n,e in blobs.items() if n not in {x['upstream_path'] for x in d['files']}],key=lambda e:e['path'])
 need(len(missing)==1033 and missing==sorted(d['outside'],key=lambda e:e['path']),'outside tree complement')
 old=json.loads((R/'frontier/sources/i72_graph_probability_discovery/inventory.json').read_text());need(sorted(old['other_blobs'],key=lambda e:e['path'])==missing,'I72 complement match')
 oldd=json.loads((R/'frontier/sources/i72_graph_probability_discovery/corpus-domain.json').read_text())
 need({e['path']:(e['sha256'],e['git_blob'],e['bytes']) for e in oldd['files']}=={e['upstream_path']:(e['sha256'],e['git_blob'],e['bytes']) for e in d['files']},'I72 domain match')
 return {'tree_entries':len(entries),'manuscripts':749,'blobs':len(blobs),'text_files':9340,'outside_blobs':1033}
def manifest():
 d={x['path']:x for x in read('corpus-domain.json')['files']};m=read('source-manifest.json')
 for e in m:
  for k in ['sha256','git_blob','bytes','upstream_path']:need(e[k]==d[e['path']][k],'manifest '+k)
  need(e['raw_url']=='https://raw.githubusercontent.com/openai/math/'+PIN+'/'+e['upstream_path'],'raw pinned URL')
 for e in read('dependencies.json'):
  s=checkfile(e['path'],e['sha256']).decode();need(gitblob(s.encode())==e['git_blob'],'dependency Git blob')
  for z in e['labels']:
   needle='\\label{'+z['label']+'}';need(needle in s,'dependency label '+needle);need(s[:s.index(needle)].count('\n')+1==z['line'],'dependency line')
 return {'selected_files':len(m),'dependency_groups':len(read('dependencies.json'))}
def passages():
 pp=read('passages.json')
 for e in pp:
  b=checkfile(e['path'],e['file_sha256']);lines=b.splitlines(keepends=True)
  need(len(lines)==e['total_lines'] and 1<=e['start']<=e['end']<=len(lines),'passage range')
  need(sha(b''.join(lines[e['start']-1:e['end']]))==e['passage_sha256'],'passage binding '+e['path'])
 coverage=read('read-coverage.json');need(coverage['status']=='INCOMPLETE_FULL_COMPANION_READ_GATE','reading status must remain candid')
 for e in coverage['files']:
  n=len((R/e['path']).read_bytes().splitlines());covered={i for b in pp if b['path']==e['path'] for i in range(b['start'],b['end']+1)}
  missed={i for a,b in e['unbound_ranges'] for i in range(a,b+1)}
  need(n==e['lines'] and len(covered)==e['bound_lines'],'coverage counts');need(not covered&missed and covered|missed==set(range(1,n+1)),'coverage partition')
 need({e['path'] for e in coverage['files']}=={e['path'] for e in read('source-manifest.json') if Path(e['path']).suffix in ['.tex','.bib']},'coverage full selected source domain')
 return {'passages':len(pp),'read_gate':coverage['status'],'bound_source_lines':sum(e['bound_lines'] for e in coverage['files']),'selected_source_lines':sum(e['lines'] for e in coverage['files'])}
def searches():
 result=[]
 for e in read('searches.json'):
  original=checkfile(e['output'],e['sha256']).decode();need(len(original.splitlines())==e['lines'],'search count')
  p=subprocess.run(['rg',*e['flags'],'--',e['pattern'],str(C)],stdout=subprocess.PIPE,stderr=subprocess.PIPE)
  need(p.returncode in [0,1],p.stderr.decode());got=p.stdout.decode().replace(str(C)+'/', '')
  need(sorted(got.splitlines())==sorted(original.splitlines()),'search replay '+e['name'])
  result.append({'name':e['name'],'hits':e['lines']})
 return result
def versions():
 vv=read('source-versions.json')
 for e in vv:
  a=(R/e['old']).read_bytes() if e['old'] else b'';b=(R/e['new']).read_bytes() if e['new'] else b''
  need(sha(a)==e['old_sha256'] and sha(b)==e['new_sha256'],'version reference hash');need((a==b)==e['equal'],'version equality')
  if 'diff' in e:
   got=''.join(difflib.unified_diff(a.decode().splitlines(True),b.decode().splitlines(True),fromfile=e['old'] or '/dev/null',tofile=e['new'] or '/dev/null')).encode()
   need(checkfile(e['diff'],e['diff_sha256'])==got,'version exact diff')
 return {'comparisons':len(vv),'identical':sum(e['equal'] for e in vv)}
def http_and_primary():
 total=0;pdfs=0
 for name in ['primary-requests.json','primary-more-requests.json','pinned-requests.json']:
  for e in read(name):
   b=checkfile(e['path'],e['sha256']);need(len(b)==e['bytes'] and e['status']==200,'response status/bytes')
   need(bool(e['headers']) and e['url'].startswith('https://') and bool(e['retrieved']),'response metadata');total+=1
   if 'upstream_reference' in e:need(b==(R/e['upstream_reference']).read_bytes() and gitblob(b)==e['git_blob'],'fresh pinned response')
   if 'conversion' in e:
    z=e['conversion'];need(z['returncode']==0,'original PDF conversion');q=subprocess.run(['pdftotext','-layout',str(R/e['path']),'-'],stdout=subprocess.PIPE,stderr=subprocess.PIPE)
    need(q.returncode==0,q.stderr.decode());need(q.stdout==(R/z['text']).read_bytes(),'exact PDF text replay '+e['path']);pdfs+=1
    if 'sha256' in z:need(sha(q.stdout)==z['sha256'],'converted hash')
 for e in read('primary-versions.json'):
  b=checkfile(e['path'],e['sha256'])
  if 'start' in e:
   lines=b.splitlines(keepends=True);need(sha(b''.join(lines[e['start']-1:e['end']]))==e['passage_sha256'],'primary history passage')
   hit=re.search(r'<div class="submission-history">(.*?)</div>',b.decode(),re.S);need(hit is not None,'submission history');need(re.findall(r'\[v(\d+)\]',hit.group(0))==e['observed_versions'],'primary version list')
 return {'HTTP_responses':total,'PDF_extractions_replayed':pdfs,'primary_version_records':len(read('primary-versions.json'))}
def diagnostics():
 env=dict(os.environ);env['PYTHONDONTWRITEBYTECODE']='1'
 p=subprocess.run([sys.executable,'-B',str(E/'diagnostics.py')],stdout=subprocess.PIPE,stderr=subprocess.PIPE,env=env)
 need(p.returncode==0,p.stderr.decode());need(p.stdout==(E/'diagnostics.json').read_bytes(),'exact diagnostic output mismatch')
 d=json.loads(p.stdout);need(d['status']=='PASS_FINITE_DIAGNOSTICS_NOT_PROOF','diagnostic status');return d
def scope_status():
 status=read('review-status.json');need(status['nomination']=='HELD' and status['accepted_count_increment']==0 and status['full_companion_read']=='INCOMPLETE','review status')
 text=REPORT.read_text();need('nomination held' in text and 'full-companion reading requirement remains incomplete' in text,'canonical report candid scope')
 need('Evidence replay PASS' in text,'proof/evidence distinction');return status
if __name__=='__main__':
 parser=argparse.ArgumentParser();parser.add_argument('--preseal',action='store_true');args=parser.parse_args()
 if not args.preseal:check('immutable assigned inventory',outer)
 for name,fn in [('inputs and immutable references',inputs),('complete tree and fixed search domain',corpus),('pinned manifest and theorem dependencies',manifest),('actual read bindings and incomplete coverage',passages),('full-domain search replay',searches),('source version comparisons',versions),('retained HTTP bytes and PDF replay',http_and_primary),('exact diagnostic replay',diagnostics),('research scope and acceptance status',scope_status)]:check(name,fn)
 result={'status':('FAIL' if failures else 'PASS_EVIDENCE_ONLY'),'mode':'preseal' if args.preseal else 'sealed_read_only','checks':checks,'failures':failures,'warning':'Not proof, significance, exhaustive novelty, full companion reading, or acceptance certification.'}
 print(json.dumps(result,indent=2,sort_keys=True));sys.exit(bool(failures))
