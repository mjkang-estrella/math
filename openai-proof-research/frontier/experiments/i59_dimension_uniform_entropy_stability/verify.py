"""Offline, read-only I59 provenance and diagnostic verification."""
from pathlib import Path
import hashlib,json,subprocess,sys,os,collections
ROOT=Path(__file__).resolve().parents[3]
S=ROOT/'frontier/sources/i59_dimension_uniform_entropy_stability'
E=ROOT/'frontier/experiments/i59_dimension_uniform_entropy_stability'
def sha(b):return hashlib.sha256(b).hexdigest()
def blob(b):return hashlib.sha1(b'blob '+str(len(b)).encode()+b'\0'+b).hexdigest()
def get(p):return json.loads(p.read_text())
def require(ok,label):
 if not ok:raise AssertionError(label)
def main():
 seal=get(S/'seal.json')
 for row in seal['artifacts']:
  require(sha((ROOT/row['path']).read_bytes())==row['sha256'],'I59 seal: '+row['path'])
 inputs=get(S/'inputs.json'); drift=[]
 for row in inputs:
  require(sha((S/'inputs'/row['path']).read_bytes())==row['sha256'],'frozen input')
  live=sha((ROOT/row['path']).read_bytes())
  if row['mutable']:
   if live!=row['sha256']:drift.append(row['path'])
  else:require(live==row['sha256'],'immutable input: '+row['path'])
 tree=get(S/'inputs/sources/preprints-tree.json')['tree']; idx={x['path']:x for x in tree}
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
 for row in get(S/'pins.json'):
  b=(S/'pinned'/row['path']).read_bytes()
  require(sha(b)==row['sha256'] and blob(b)==row['git_blob']==idx[row['path']]['sha'],'selected pin')
 for row in get(S/'prior-hashes.json'):
  require(sha((ROOT/row['path']).read_bytes())==row['sha256'],'prior unchanged: '+row['path'])
 searches=get(S/'searches.json')
 for row in searches:
  cp=subprocess.run(['rg','--no-ignore','-n','-i',row['pattern'],'.'],cwd=corpus,text=True,capture_output=True)
  require(cp.returncode in (0,1),'rg status')
  require(collections.Counter(cp.stdout.splitlines())==collections.Counter(get(S/'searches'/(row['label']+'.json'))),'search multiset')
 manifest=get(S/'literature/manifest.json'); pdf_count=0
 for row in manifest:
  if 'path' not in row:continue
  require(sha((ROOT/row['path']).read_bytes())==row['sha256'],'primary response bytes')
  if 'text_path' in row:
   raw=subprocess.check_output(['pdftotext','-layout',str(ROOT/row['path']),'-'])
   require(sha(raw)==row['text_sha256'],'PDF text replay: '+row['name'])
   require(raw==(ROOT/row['text_path']).read_bytes(),'PDF stored text')
   pdf_count+=1
 passages=get(S/'passages.json')
 for row in passages:
  lines=(ROOT/row['path']).read_text().splitlines(keepends=True)
  passage=''.join(lines[row['start']-1:row['end']])
  require(passage==row['text'] and sha(passage.encode())==row['sha256'],'proof passage')
 env=dict(os.environ,PYTHONDONTWRITEBYTECODE='1')
 output=subprocess.check_output([sys.executable,str(E/'diagnostics.py')],cwd=ROOT,env=env)
 require(output==(E/'diagnostics.json').read_bytes(),'independent diagnostics replay')
 diag=json.loads(output)
 return dict(status='PASS',artifacts=len(seal['artifacts']),inputs=len(inputs),mutable_ledger_drift=drift,
  tree_entries=len(tree),manuscripts=749,corpus_files=len(inventory),selected_pins=len(get(S/'pins.json')),
  prior_files=len(get(S/'prior-hashes.json')),search_multisets=[r['lines'] for r in searches],
  primary_responses=len(manifest),pdf_replays=pdf_count,passages=len(passages),
  exact_assertions=diag['exact_assertions'],floating_family_records=len(diag['families']),
  limitation='Provenance and finite diagnostics only. U unproved and unrefuted; no analytic independent review claimed.')
if __name__=='__main__':
 try: print(json.dumps(main(),indent=2,sort_keys=True))
 except Exception as exc:
  print(json.dumps(dict(status='FAIL',error=str(exc)),indent=2));sys.exit(1)
