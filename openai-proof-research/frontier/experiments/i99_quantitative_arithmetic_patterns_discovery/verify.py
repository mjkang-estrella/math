"""I99 OFFLINE READ-ONLY verifier. No write/download/repair/reseal modes.
Run with python -B. Sealing and evidence preparation are separate, never invoked here.
Source integrity and finite diagnostics do not certify analytic proofs or contribution.
"""
from pathlib import Path
import hashlib,json,re,subprocess,sys
sys.dont_write_bytecode=True
S=Path('frontier/sources/i99_quantitative_arithmetic_patterns_discovery')
E=Path('frontier/experiments/i99_quantitative_arithmetic_patterns_discovery')
REPORT=Path('frontier/iterations/i99-quantitative-arithmetic-patterns-discovery.md')
SEAL=S/'seal.json'
MUTABLE={'README.md','frontier/README.md','frontier/TEN-FINDINGS.md','frontier/iterations/README.md'}
def sha(b):return hashlib.sha256(b).hexdigest()
def readj(p):return json.loads(p.read_text())
def owned():
 return sorted([str(REPORT)]+[str(p) for r in [S,E] for p in r.rglob('*') if p.is_file() and p!=SEAL])
def inventory():
 return [{'path':p,'sha256':sha(Path(p).read_bytes()),'size':Path(p).stat().st_size} for p in owned()]
def verify_semantics():
 failures=[];stats={};drifts=[]
 def need(test,label):
  if not test:failures.append(label)
 domain=readj(S/'search-domain.json')
 tree=readj(S/'snapshots/sources/preprints-tree.json')
 blobs={x['path']:x['sha'] for x in tree['tree'] if x['type']=='blob'}
 manuscripts={x['path'].split('/')[1] for x in tree['tree'] if x['path'].startswith('preprints/')}
 need(len(tree['tree'])==13223,'tree entry count')
 need(len(manuscripts)==749,'manuscript count')
 need(len(blobs)==len(domain)==10373,'blob/domain counts')
 need(set(blobs)=={x['path'] for x in domain},'exact domain coverage')
 corpus={x['original_local'] for x in domain if x['kind']=='corpus'}
 actual=set(subprocess.run(['rg','--files','--no-ignore','frontier/sources/i14_spectral_width_novelty_r3/corpus'],check=True,stdout=subprocess.PIPE,text=True).stdout.splitlines())
 need(actual==corpus and len(corpus)==9340,'exact reused I14 inventory')
 searches=readj(S/'lexical-search.json')
 expected_expressions=[r'intersectiv',r'polynomial.{0,30}(progression|configuration|pattern|difference)',r'(simultaneous|joint).{0,40}(square.?free|power.?free|polynomial)',r'(uniform|height).{0,40}(polynomial|coefficient)',r'Szemer',r'square.difference']
 need([x['expression'] for x in searches]==expected_expressions,'exact expression list')
 rx=[re.compile(e,re.I) for e in expected_expressions];hits=[[] for _ in rx]
 for row in domain:
  p=Path(row['original_local']);b=p.read_bytes()
  need(sha(b)==row['original_sha256'],'original sha256: '+str(p))
  git=hashlib.sha1(b'blob '+str(len(b)).encode()+b'\0'+b).hexdigest()
  need(git==row['git_sha']==blobs[row['path']],'git identity: '+row['path'])
  text_bytes=b if row['local']==row['original_local'] else Path(row['local']).read_bytes()
  need(sha(text_bytes)==row['sha256'],'text sha256: '+row['local'])
  for ln,line in enumerate(text_bytes.decode(errors='replace').splitlines(),1):
   for j,r in enumerate(rx):
    for m in r.finditer(line):
     hits[j].append({'path':row['path'],'line_splitlines':ln,'start':m.start(),'match':m.group(),'text':line})
 for j,item in enumerate(searches):
  need(item['flags']=='IGNORECASE','regex flags')
  need(item['occurrences']==hits[j],'exact search occurrence multiset/order '+str(j))
 stats.update(tree_entries=len(tree['tree']),manuscripts=len(manuscripts),original_blob_positions=len(domain),corpus_originals=len(corpus),search_occurrences=[len(x) for x in hits])
 for row in readj(S/'references.json'):
  snap=Path(row['snapshot']).read_bytes()
  need(sha(snap)==row['sha256'],'immutable snapshot '+row['snapshot'])
  need(row['may_drift']==(row['path'] in MUTABLE),'reference drift policy '+row['path'])
  now=sha(Path(row['path']).read_bytes())
  if now!=row['sha256']:
   if row['may_drift']:drifts.append({'path':row['path'],'snapshot_sha256':row['sha256'],'live_sha256':now})
   else:failures.append('immutable reference drift '+row['path'])
 passages=readj(S/'passages.json')
 for item in passages:
  b=Path(item['local']).read_bytes();lines=b.decode().split('\n')
  if lines[-1]=='':lines.pop()
  excerpt='\n'.join(lines[item['start']-1:item['end']])
  need(sha(b)==item['sha256'],'passage source '+item['local'])
  need(len(lines)==item['total_lf_lines'],'passage LF count '+item['local'])
  need(excerpt==item['excerpt'] and sha(excerpt.encode())==item['excerpt_sha256'],'passage bytes '+item['local'])
  need(item['git_sha']==blobs[item['path']],'passage git reference')
  need(item['url']=='https://raw.githubusercontent.com/openai/math/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/'+item['path'],'pinned passage URL')
 pdfs=readj(S/'pdf-replay.json')
 need(len(pdfs)==4,'selective PDF replay scope')
 for item in pdfs:
  b=subprocess.run(['pdftotext','-layout',item['original'],'-'],check=True,stdout=subprocess.PIPE).stdout
  need(sha(b)==item['sha256'] and b==Path(item['text']).read_bytes(),'selected PDF extraction '+item['original'])
 for item in readj(S/'literature/retrieval.json'):
  need(sha(Path(item['path']).read_bytes())==item['sha256'],'primary response hash '+item['path'])
 for item in readj(S/'literature-texts.json'):
  b=Path(item['path']).read_bytes();t=b.decode()
  need(sha(b)==item['sha256'],'literature text hash')
  need(len(t.splitlines())==item['splitlines_count'],'literature splitlines count')
  need(len(t.split('\n'))-t.endswith('\n')==item['lf_lines'],'literature LF count')
 ns={'__name__':'i99_exact_diagnostics'}
 exec(compile((E/'diagnostics.py').read_bytes(),str(E/'diagnostics.py'),'exec'),ns)
 result=ns['run']()
 need(result==readj(E/'diagnostics-result.json'),'finite diagnostic replay')
 stats.update(passages=len(passages),selective_pdf_replays=len(pdfs),finite_diagnostics=result['counts'])
 return {'status':'PASS' if not failures else 'FAIL','failures':failures,'allowed_live_ledger_drift':drifts,'checks':stats,'scope':'integrity and finite exact checks only; no analytic proof/novelty certification'}
def verify():
 seal=readj(SEAL)
 failures=[]
 if seal['schema']!='i99-seal-v1':failures.append('seal schema')
 if seal['inventory']!=inventory():failures.append('exact owned inventory or byte hashes differ')
 if any(Path(x).is_symlink() for x in owned()):failures.append('owned symbolic link')
 result=verify_semantics()
 result['failures']=failures+result['failures']
 result['status']='PASS' if not result['failures'] else 'FAIL'
 result['owned_inventory_files']=len(seal['inventory'])
 result['seal_sha256']=sha(SEAL.read_bytes())
 return result
if __name__=='__main__':
 try:result=verify()
 except Exception as exc:result={'status':'FAIL','exception':type(exc).__name__+': '+str(exc)}
 print(json.dumps(result,indent=2,sort_keys=True))
 sys.exit(0 if result['status']=='PASS' else 1)
