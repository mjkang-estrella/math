#!/usr/bin/env python3
"""Offline READ-ONLY verifier. No fetch, writes, repair or reseal.
Run from anywhere. Prints evidence verdict, never a mathematical proof verdict.
"""
from pathlib import Path
import hashlib,json,re,subprocess,sys,os,collections
ROOT=Path(__file__).resolve().parents[3]
S='frontier/sources/i82_measured_group_operator_discovery'
E='frontier/experiments/i82_measured_group_operator_discovery'
REPORT='frontier/iterations/i82-measured-group-operator-discovery.md'
def read(p):return (ROOT/p).read_bytes()
def sha(b):return hashlib.sha256(b).hexdigest()
def js(p):return json.loads(read(p))
def check(c,msg):
 if not c:raise AssertionError(msg)
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
 preseal=sys.argv[1:]==['--preseal']
 check(not sys.argv[1:] or preseal,'unknown arguments')
 if preseal:
  check(not (ROOT/sealpath).exists(),'preseal mode forbidden after seal exists')
  stats['unsealed_preflight_files']=len(owned())
 else:
  check(read(anchorpath).decode().strip()==sha(read(sealpath)),'seal anchor')
  seal=js(sealpath); check(seal['exclusions']==[sealpath,anchorpath],'seal exclusions')
  files=seal['files'];check(owned()==set(files)|{sealpath,anchorpath},'exact owned domain')
  for p,h in files.items():check(sha(read(p))==h,'sealed '+p)
  stats['sealed_files']=len(files)
 for x in js(S+'/inputs.json'):
  check(sha(read(x['snapshot']))==x['sha256'],'input snapshot '+x['path'])
  if sha(read(x['path']))!=x['sha256']:
   check(x['mutable'] and x['path'] in ['README.md','frontier/README.md','frontier/TEN-FINDINGS.md','frontier/iterations/README.md'],'immutable input '+x['path']);drift.append(x['path'])
 for x in js(S+'/immutable-references.json'):check(sha(read(x['path']))==x['sha256'],'reference '+x['path'])
 tree=js('sources/preprints-tree.json');check(not tree['truncated'],'truncated tree')
 blobs={x['path']:x for x in tree['tree'] if x['type']=='blob'}
 check(len(tree['tree'])==13223 and len(blobs)==10373,'tree inventory')
 check(len({p.split('/')[1] for p in blobs})==749,'manuscript inventory')
 domain=js('frontier/sources/i79_logarithmic_girth_spectra_novelty_r3/search-domain.json')
 check(len(domain)==len(blobs) and {x['path']for x in domain}==set(blobs),'search coverage')
 checks=js(S+'/searches.json');patterns={x['name']:re.compile(x['pattern'],re.I)for x in checks};hits={x['name']:[]for x in checks}
 corpus=[]
 for x in domain:
  b=read(x['local']);check(sha(b)==x['sha256'],'domain '+x['local'])
  if x['kind']=='corpus':
   check(hashlib.sha1(b'blob '+str(len(b)).encode()+b'\0'+b).hexdigest()==blobs[x['path']]['sha'],'corpus Git '+x['path']);corpus.append(x['local'])
  for i,line in enumerate(b.decode('utf-8',errors='replace').splitlines(),1):
   for name,rx in patterns.items():
    if rx.search(line):hits[name].append(dict(path=x['path'],local=x['local'],line=i,text=line))
 stats['corpus_git_blobs']=len(corpus)
 inventory=read(S+'/corpus-rg-files.txt').decode().splitlines();check(sorted(corpus)==sorted(inventory),'retained rg corpus inventory')
 current=subprocess.run(['rg','--files','--no-ignore','frontier/sources/i14_spectral_width_novelty_r3/corpus'],cwd=ROOT,capture_output=True,check=True).stdout.decode().splitlines()
 check(sorted(current)==sorted(inventory),'live corpus exact domain')
 requests=[json.loads(l) for l in read('frontier/sources/i79_logarithmic_girth_spectra_novelty_r3/outside-requests.jsonl').decode().splitlines()]
 check(len(requests)==1033 and len({x['path']for x in requests})==1033,'outside inventory')
 for x in requests:
  b=read(x['local']);check(x['status']==200 and x['git_match'],'outside response')
  check(sha(b)==x['sha256'],'outside SHA '+x['path'])
  check(hashlib.sha1(b'blob '+str(len(b)).encode()+b'\0'+b).hexdigest()==blobs[x['path']]['sha']==x['sha'],'outside Git '+x['path'])
  if 'extraction' in x:check(sha(read(x['extraction']['path']))==x['extraction']['sha256'],'outside extraction '+x['path'])
 stats['outside_git_blobs']=len(requests);stats['outside_pdf_extractions']=sum('extraction'in x for x in requests)
 for x in checks:
  check(len(hits[x['name']])==x['lines'],'search hit count '+x['name'])
  # Multisets retain duplicates, do not rely on filesystem order.
  key=lambda y:json.dumps(y,sort_keys=True,ensure_ascii=False)
  check(collections.Counter(map(key,hits[x['name']]))==collections.Counter(map(key,js(x['output']))),'search multiset '+x['name'])
  check(sha(read(x['output']))==x['sha256'],'search body '+x['name'])
 stats['search_lines']={x['name']:x['lines']for x in checks}
 for x in js(S+'/source-references.json'):
  b=read(x['local']);check(sha(b)==x['sha256'],'source SHA')
  check(hashlib.sha1(b'blob '+str(len(b)).encode()+b'\0'+b).hexdigest()==x['git_blob']==blobs[x['path']]['sha'],'source Git')
 for x in js(S+'/source-contracts.json'):
  t=read(x['local']).decode();check(x['text']in t and sha(x['text'].encode())==x['sha256'],'contract')
  check(x['text'] in ''.join(t.splitlines(keepends=True)[x['start']-1:x['end']]),'contract line binding')
 passages=js(S+'/passages.json')
 for x in passages:
  lines=read(x['local']).decode().splitlines(keepends=True);check(sha(''.join(lines[x['start']-1:x['end']]).encode())==x['sha256'],'passage '+x['local'])
 stats['passages']=len(passages)
 primary=[json.loads(l)for l in read(S+'/primary-requests.jsonl').decode().splitlines()]
 replays=0
 for x in primary:
  check(sha(read(x['local']))==x['sha256'],'primary response')
  check(len(read(x['local']))==x['bytes'],'primary size')
  if 'extraction'in x:
   q=x['extraction'];check(q['code']==0 and sha(read(q['local']))==q['sha256'],'primary extraction')
   out=subprocess.run(['pdftotext','-layout',str(ROOT/x['local']),'-'],capture_output=True,check=True).stdout
   check(sha(out)==q['sha256'],'primary PDF replay');replays+=1
 stats['primary_responses']=len(primary);stats['primary_pdf_replays']=replays
 # Replay selected upstream PDFs, all other 776 extraction identities were checked above.
 selected={x['path']for x in js(S+'/selected-domain.json')if x['kind']=='outside_pdf'};n=0
 for x in requests:
  if x['path']in selected:
   out=subprocess.run(['pdftotext','-layout',str(ROOT/x['local']),'-'],capture_output=True,check=True).stdout
   check(sha(out)==x['extraction']['sha256'],'selected upstream PDF replay '+x['path']);n+=1
 stats['selected_upstream_pdf_replays']=n
 for x in js(S+'/versions.json'):check(sha(read(x['local']))==x['sha256'],'version-page binding')
 env=dict(os.environ,PYTHONDONTWRITEBYTECODE='1')
 out=subprocess.run([sys.executable,str(ROOT/E/'diagnostics.py')],cwd=ROOT,env=env,capture_output=True,check=True).stdout
 check(out==read(E+'/output.json'),'diagnostics exact replay');stats['diagnostics']=json.loads(out)
 print(json.dumps(dict(evidence='PRESEAL PASS' if preseal else 'PASS',original_proof='AUTHOR PROOF ONLY; no independent verdict',contribution='TECHNICAL author assessment; no substantial nomination',stats=stats,mutable_ledger_drift=drift,read_only=True,network=False),indent=2,sort_keys=True))
except Exception as ex:
 print(json.dumps(dict(evidence='FAIL',error=repr(ex),stats=stats,mutable_ledger_drift=drift,read_only=True,network=False),indent=2,sort_keys=True));sys.exit(1)
