#!/usr/bin/env python3
"""Offline READ-ONLY integrity/replay check. No fetch, writes, repair or reseal.
Evidence PASS is not a proof verdict. --preseal is forbidden once seal exists.
"""
from pathlib import Path
import hashlib,json,re,subprocess,sys,os,collections
ROOT=Path(__file__).resolve().parents[3]
S='frontier/sources/i84_abstract_close_algebras';E='frontier/experiments/i84_abstract_close_algebras'
REPORT='frontier/iterations/i84-abstract-close-algebras.md'
MUTABLE=['README.md','frontier/README.md','frontier/TEN-FINDINGS.md','frontier/iterations/README.md']
def read(p):return (ROOT/p).read_bytes()
def sha(b):return hashlib.sha256(b).hexdigest()
def js(p):return json.loads(read(p))
def check(ok,msg):
 if not ok:raise AssertionError(msg)
def gitsha(b):return hashlib.sha1(b'blob '+str(len(b)).encode()+b'\0'+b).hexdigest()
def owned():
 out={REPORT}
 for base in [S,E]:
  for p in (ROOT/base).rglob('*'):
   check(not p.is_symlink(),'owned symlink '+str(p))
   if p.is_file():out.add(p.relative_to(ROOT).as_posix())
 return out
stats={};drift=[]
try:
 sealpath=S+'/seal-v1.json';anchorpath=S+'/seal-v1.sha256'
 preseal=sys.argv[1:]==['--preseal'];check(not sys.argv[1:] or preseal,'arguments')
 if preseal:
  check(not (ROOT/sealpath).exists() and not (ROOT/anchorpath).exists(),'preseal forbidden after sealing')
  stats['unsealed_preflight_files']=len(owned())
 else:
  check(read(anchorpath).decode().strip()==sha(read(sealpath)),'seal anchor')
  seal=js(sealpath);check(seal['exclusions']==[sealpath,anchorpath],'seal exclusions')
  check(seal['owned_report']==REPORT and seal['owned_directories']==[S,E],'declared ownership')
  files=seal['files'];check(owned()==set(files)|{sealpath,anchorpath},'exact owned domain')
  for p,h in files.items():check(sha(read(p))==h,'sealed '+p)
  stats['sealed_files']=len(files)
 for x in js(S+'/inputs.json'):
  check(sha(read(x['snapshot']))==x['sha256'],'input snapshot '+x['path'])
  if sha(read(x['path']))!=x['sha256']:
   check(x['mutable'] and x['path'] in MUTABLE,'immutable input '+x['path']);drift.append(x['path'])
 for x in js(S+'/immutable-references.json'):check(sha(read(x['path']))==x['sha256'],'immutable reference '+x['path'])
 # Original author artifacts, independently bound and never repaired.
 old82=js('frontier/sources/i82_measured_group_operator_discovery/seal-v1.json')
 for p,h in old82['files'].items():check(sha(read(p))==h,'original I82 artifact '+p)
 old79=js('frontier/sources/i79_logarithmic_girth_spectra_novelty_r3/seal-v1.json')
 for x in old79['artifacts']:
  b=read(x['path']);check(len(b)==x['bytes'] and sha(b)==x['sha256'],'original I79 artifact '+x['path'])
 stats['immutable_original_artifacts']={'I82':len(old82['files']),'I79':len(old79['artifacts'])}
 tree=js('sources/preprints-tree.json');check(not tree['truncated'],'truncated tree')
 blobs={x['path']:x for x in tree['tree'] if x['type']=='blob'}
 check(len(tree['tree'])==13223 and len(blobs)==10373,'full tree counts')
 check(len({p.split('/')[1] for p in blobs})==749,'full manuscript count')
 domain=js('frontier/sources/i79_logarithmic_girth_spectra_novelty_r3/search-domain.json')
 check(len(domain)==10373 and {x['path'] for x in domain}==set(blobs),'full search domain')
 checks=js(S+'/searches.json');patterns={x['name']:re.compile(x['pattern'],re.I) for x in checks};hits={k:[] for k in patterns};corpus=[]
 for x in domain:
  b=read(x['local']);check(sha(b)==x['sha256'],'search domain hash '+x['path'])
  if x['kind']=='corpus':
   check(gitsha(b)==blobs[x['path']]['sha'],'corpus Git '+x['path']);corpus.append(x['local'])
  for n,line in enumerate(b.decode('utf8',errors='replace').splitlines(),1):
   for name,rx in patterns.items():
    if rx.search(line):hits[name].append(dict(path=x['path'],local=x['local'],line=n,text=line))
 stats['corpus_git_blobs']=len(corpus)
 inv=read(S+'/corpus-rg-files.txt').decode().splitlines()
 check(sorted(inv)==sorted(corpus),'captured corpus inventory')
 live=subprocess.run(['rg','--files','--no-ignore','frontier/sources/i14_spectral_width_novelty_r3/corpus'],cwd=ROOT,capture_output=True,check=True).stdout.decode().splitlines()
 check(sorted(live)==sorted(inv),'exact live corpus inventory')
 requests=[json.loads(l) for l in read('frontier/sources/i79_logarithmic_girth_spectra_novelty_r3/outside-requests.jsonl').decode().splitlines()]
 check(len(requests)==1033 and len({x['path'] for x in requests})==1033,'outside inventory')
 for x in requests:
  b=read(x['local']);check(x['status']==200 and x['git_match'],'outside response status')
  check(sha(b)==x['sha256'],'outside SHA '+x['path'])
  check(gitsha(b)==blobs[x['path']]['sha']==x['sha'],'outside Git '+x['path'])
  if 'extraction' in x:check(sha(read(x['extraction']['path']))==x['extraction']['sha256'],'outside extraction '+x['path'])
 stats['outside_git_blobs']=len(requests);stats['outside_pdf_extractions']=sum('extraction' in x for x in requests)
 key=lambda y:json.dumps(y,sort_keys=True,ensure_ascii=False)
 for x in checks:
  check(len(hits[x['name']])==x['lines'],'search count '+x['name'])
  check(collections.Counter(map(key,hits[x['name']]))==collections.Counter(map(key,js(x['output']))),'full search multiset '+x['name'])
  check(sha(read(x['output']))==x['sha256'],'search output hash '+x['name'])
 stats['search_lines']={x['name']:x['lines'] for x in checks}
 domainmap={x['path']:x for x in domain}
 selected=js(S+'/selected-domain.json')
 for x in selected:check(x==domainmap[x['path']],'selected corpus binding')
 selectedpdfs={x['path'] for x in selected if x['kind']=='outside_pdf'};replays=0
 for x in requests:
  if x['path'] in selectedpdfs:
   out=subprocess.run(['pdftotext','-layout',str(ROOT/x['local']),'-'],capture_output=True,check=True).stdout
   check(sha(out)==x['extraction']['sha256'],'selected PDF extraction replay '+x['path']);replays+=1
 stats['selected_upstream_pdf_replays']=replays
 for x in js(S+'/source-references.json'):
  b=read(x['local']);check(sha(b)==x['sha256'],'source reference hash')
  check(gitsha(b)==x['git_blob']==blobs[x['path']]['sha'],'source Git binding')
 for x in js(S+'/source-contracts.json'):
  t=read(x['local']).decode();lines=t.splitlines(keepends=True)
  check(''.join(lines[x['start']-1:x['end']])==x['text'] and sha(x['text'].encode())==x['sha256'],'source contract '+x['label'])
 passages=js(S+'/passages.json')
 for x in passages:
  b=read(x['local']);check(sha(b)==x['source_sha256'],'passage source '+x['label'])
  t=''.join(b.decode().splitlines(keepends=True)[x['start']-1:x['end']])
  check(t==x['text'] and sha(t.encode())==x['sha256'],'bound passage '+x['label'])
 stats['passages']=len(passages)
 primary=[json.loads(l) for l in read(S+'/primary-requests.jsonl').decode().splitlines()];replays=0;fail=[]
 for x in primary:
  if 'local' not in x:
   check('error' in x,'missing response');fail.append(x['url']);continue
  b=read(x['local']);check(sha(b)==x['sha256'] and len(b)==x['bytes'],'primary retained body '+x['local'])
  if x.get('status')!=200:fail.append(x['url'])
  if 'extraction' in x:
   q=x['extraction'];check(q['code']==0 and sha(read(q['local']))==q['sha256'],'primary extraction identity')
   out=subprocess.run(['pdftotext','-layout',str(ROOT/x['local']),'-'],capture_output=True,check=True).stdout
   check(sha(out)==q['sha256'],'primary PDF replay');replays+=1
 for x in js(S+'/inherited-primary.json'):
  check(sha(read(x['local']))==x['sha256'],'inherited primary PDF')
  check(sha(read(x['extraction']))==x['extraction_sha256'],'inherited primary extraction')
  out=subprocess.run(['pdftotext','-layout',str(ROOT/x['local']),'-'],capture_output=True,check=True).stdout
  check(sha(out)==x['extraction_sha256'],'inherited primary replay')
 stats['primary_responses']=len(primary);stats['primary_pdf_replays']=replays;stats['inherited_primary_pdf_replays']=len(js(S+'/inherited-primary.json'));stats['retained_http_failures']=fail
 for x in js(S+'/versions.json'):
  b=read(x['local']);check(sha(b)==x['sha256'],'version page hash');t=b.decode()
  check(x['observed_version_url'] in t and x['history_html'] in t,'version history binding')
 for x in js(S+'/visual-readings.json'):
  n=str(x['page_index_1based']);out=subprocess.run(['pdftoppm','-f',n,'-l',n,'-r',str(x['dpi']),'-png','-singlefile',str(ROOT/x['pdf'])],capture_output=True,check=True).stdout
  check(sha(read(x['local']))==x['sha256']==sha(out),'scanned-page render replay')
 stats['scanned_page_render_replays']=len(js(S+'/visual-readings.json'))
 out=subprocess.run([sys.executable,'-B',str(ROOT/E/'diagnostics.py')],cwd=ROOT,env=dict(os.environ,PYTHONDONTWRITEBYTECODE='1'),capture_output=True,check=True).stdout
 check(out==read(E+'/output.json'),'exact diagnostic replay');stats['diagnostics']=json.loads(out)
 print(json.dumps(dict(evidence='PRESEAL PASS' if preseal else 'PASS',original_I82_section9='PASS ORIGINAL WITHOUT REPAIRS (scoped author audit)',A84='AUTHOR PROOF; independent review pending',contribution='TECHNICAL; no substantial nomination',stats=stats,mutable_ledger_drift=drift,network=False,read_only=True),sort_keys=True,indent=2))
except Exception as ex:
 print(json.dumps(dict(evidence='FAIL',error=repr(ex),stats=stats,mutable_ledger_drift=drift,network=False,read_only=True),sort_keys=True,indent=2));sys.exit(1)
