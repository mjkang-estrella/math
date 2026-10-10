"""Offline, read-only I61 provenance and finite-diagnostic replay."""
from pathlib import Path
import hashlib,json,subprocess,sys,os,collections,re
ROOT=Path(__file__).resolve().parents[3]
S=ROOT/'frontier/sources/i61_averaged_entropy_coefficient_rounding'
E=ROOT/'frontier/experiments/i61_averaged_entropy_coefficient_rounding'
REPORT=ROOT/'frontier/iterations/i61-averaged-entropy-coefficient-rounding.md'
def sha(b):return hashlib.sha256(b).hexdigest()
def blob(b):return hashlib.sha1(b'blob '+str(len(b)).encode()+b'\0'+b).hexdigest()
def get(p):return json.loads(p.read_text())
def require(ok,label):
 if not ok:raise AssertionError(label)
def main():
 seal=get(S/'seal.json')
 excluded={S/'seal.json',E/'verification.json'}
 actual={str(p.relative_to(ROOT)) for folder in [S,E] for p in folder.rglob('*') if p.is_file() and p not in excluded}|{str(REPORT.relative_to(ROOT))}
 require(actual=={r['path'] for r in seal['artifacts']},'complete I61 sealed artifact inventory')
 for row in seal['artifacts']:
  require(sha((ROOT/row['path']).read_bytes())==row['sha256'],'I61 seal: '+row['path'])
 inputs=get(S/'inputs.json');drift=[]
 for row in inputs:
  require(sha((S/'inputs'/row['path']).read_bytes())==row['sha256'],'frozen input')
  live=sha((ROOT/row['path']).read_bytes())
  if row['mutable']:
   if live!=row['sha256']:drift.append(row['path'])
  else:require(live==row['sha256'],'immutable input: '+row['path'])
 require(sum(r['mutable'] for r in inputs)==4,'exactly four mutable ledgers')
 task=get(S/'inputs/frontier/iterations/iteration61-averaged-entropy-coefficient-rounding-task.json')
 require((S/'brief.txt').read_text()=='Act as the research sub-agent for this task.\n\n'+task['brief'],'complete original assignment')
 tree=get(S/'inputs/sources/preprints-tree.json')['tree'];idx={x['path']:x for x in tree}
 require(len(tree)==13223,'complete tree count')
 require(len({x['path'].split('/')[1] for x in tree})==749,'manuscript count')
 corpus=ROOT/'frontier/sources/i14_spectral_width_novelty_r3/corpus'
 actual=sorted(x.removeprefix('./') for x in subprocess.check_output(['rg','--files','--no-ignore','.'],cwd=corpus,text=True).splitlines())
 inventory=get(S/'corpus.json')
 require(actual==sorted(x['path'] for x in inventory),'corpus path inventory')
 require(len(actual)==9340,'corpus count')
 for row in inventory:
  b=(corpus/row['path']).read_bytes()
  require(sha(b)==row['sha256'],'corpus sha: '+row['path'])
  require(blob(b)==row['git_blob']==idx[row['path']]['sha'],'corpus Git blob: '+row['path'])
 pins=get(S/'pins.json')+get(S/'additional-pins.json')
 for row in pins:
  b=(S/'pinned'/row['path']).read_bytes()
  require(sha(b)==row['sha256'] and blob(b)==row['git_blob']==idx[row['path']]['sha'],'selected pin')
 for row in get(S/'prior-hashes.json'):
  require(sha((ROOT/row['path']).read_bytes())==row['sha256'],'prior unchanged: '+row['path'])
 for row in get(S/'prior-records.json'):
  require(sha((ROOT/row['path']).read_bytes())==sha((ROOT/row['original']).read_bytes())==row['sha256'],'frozen original brief/objections')
 searches=get(S/'searches.json')
 for row in searches:
  cp=subprocess.run(['rg','--no-ignore','-n','-i',row['pattern'],'.'],cwd=corpus,text=True,capture_output=True)
  require(cp.returncode in (0,1),'rg status')
  saved=get(S/'searches'/(row['label']+'.json'))
  require(len(saved)==row['lines'],'search line count')
  require(collections.Counter(cp.stdout.splitlines())==collections.Counter(saved),'search multiset')
 manifest=get(S/'literature/manifest.json');raw_manifest=get(S/'primary-pinned/manifest.json');pdf_count=0
 for row in manifest+raw_manifest:
  if 'path' not in row:
   require('error' in row,'explicit retrieval failure record');continue
  b=(ROOT/row['path']).read_bytes()
  require(sha(b)==row['sha256'],'primary response bytes')
  if 'actual_git_blob' in row:
   require(blob(b)==row['actual_git_blob']==row['expected_git_blob'] and row['matches_pin'],'fresh pinned response')
  if 'text_path' in row:
   raw=subprocess.check_output(['pdftotext','-layout',str(ROOT/row['path']),'-'],stderr=subprocess.PIPE)
   require(sha(raw)==row['text_sha256'],'PDF text replay: '+row['name'])
   require(raw==(ROOT/row['text_path']).read_bytes(),'PDF stored text')
   pdf_count+=1
 for row in get(S/'literature/versions.json'):
  match=re.search(r'arXiv:[0-9.]+v\d+[^\n]*',(ROOT/row['path']).read_text())
  require(match and match.group(0)==row['served_version'],'served primary version')
 passages=get(S/'passages.json')
 for row in passages:
  lines=(ROOT/row['path']).read_text().splitlines(keepends=True)
  passage=''.join(lines[row['start']-1:row['end']])
  require(passage==row['text'] and sha(passage.encode())==row['sha256'],'exact proof passage')
 contracts=get(S/'read-contracts.json')
 for row in contracts:
  require(sha((ROOT/row['path']).read_bytes())==row['sha256'],'read-contract source')
  for a,b in row['ranges']:
   require(any(p['path']==row['path'] and p['start']==a and p['end']==b for p in passages),'read-contract passage coverage')
 env=dict(os.environ,PYTHONDONTWRITEBYTECODE='1')
 output=subprocess.check_output([sys.executable,str(E/'diagnostics.py')],cwd=ROOT,env=env)
 require(output==(E/'diagnostics.json').read_bytes(),'deterministic finite diagnostics replay')
 diag=json.loads(output)
 return dict(status='PASS',artifacts=len(seal['artifacts']),inputs=len(inputs),mutable_ledger_drift=drift,
  tree_entries=len(tree),manuscripts=749,corpus_files=len(inventory),selected_pins=len(pins),
  prior_files=len(get(S/'prior-hashes.json')),prior_brief_objection_copies=len(get(S/'prior-records.json')),
  search_multisets=[r['lines'] for r in searches],primary_responses=len(manifest)+len(raw_manifest),
  successful_primary_responses=sum(r.get('status')==200 for r in manifest+raw_manifest),
  pdf_replays=pdf_count,passages=len(passages),read_contracts=len(contracts),
  exact_assertions=diag['exact_assertions'],floating_records=len(diag['floating_records']),
  limitation='Provenance and finite diagnostics only. CE61 is an author proof awaiting independent analytic/contribution review; AR and U unproved and unrefuted. No accepted-count change.')
if __name__=='__main__':
 try:print(json.dumps(main(),indent=2,sort_keys=True))
 except Exception as exc:
  print(json.dumps(dict(status='FAIL',error=str(exc)),indent=2));sys.exit(1)
