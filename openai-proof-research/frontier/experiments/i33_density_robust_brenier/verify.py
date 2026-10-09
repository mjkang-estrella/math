"""Integrity and finite-diagnostic verifier. This does not certify the analytic proofs."""
from pathlib import Path
from fractions import Fraction as F
import hashlib,json,sys,urllib.parse

ROOT=Path(__file__).resolve().parents[3]
S=ROOT/'frontier/sources/i33_density_robust_brenier'
E=ROOT/'frontier/experiments/i33_density_robust_brenier'
REPORT=ROOT/'frontier/iterations/i33-density-robust-brenier.md'
CORPUS=ROOT/'frontier/sources/i14_spectral_width_novelty_r3/corpus'
SEAL=S/'artifact-seal.json'
PIN='fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb'
EXCLUDE={SEAL,E/'verification.json',E/'live-drift.json'}

def sha(b):return hashlib.sha256(b).hexdigest()
def blob(b):return hashlib.sha1(b'blob '+str(len(b)).encode()+b'\0'+b).hexdigest()
def read(p):return json.loads(p.read_text())
def artifacts():
 return sorted([p for folder in (S,E) for p in folder.rglob('*') if p.is_file() and p not in EXCLUDE and '__pycache__' not in p.parts]+[REPORT])
def ident(p):return {'path':str(p.relative_to(ROOT)),'sha256':sha(p.read_bytes()),'bytes':p.stat().st_size}

def main():
 if '--seal' in sys.argv:
  SEAL.write_text(json.dumps({'scope':'I33 assigned outputs only; verifier output and live drift excluded; no mathematical certification','files':[ident(p) for p in artifacts()]},indent=2)+'\n')
 errors=[];drift=[]
 def require(test,msg):
  if not test:errors.append(msg)
 def check(row):
  p=ROOT/row['path'];require(p.is_file(),'missing '+str(p))
  if p.is_file():
   b=p.read_bytes();require(sha(b)==row['sha256'],'SHA '+row['path'])
   if 'bytes' in row:require(len(b)==row['bytes'],'size '+row['path'])
 require(SEAL.exists(),'missing seal')
 seal=read(SEAL)
 for row in seal['files']:check(row)
 require({r['path'] for r in seal['files']}=={str(p.relative_to(ROOT)) for p in artifacts()},'artifact inventory mismatch')
 inputs=read(S/'input-manifest.json')
 for row in inputs:
  check({'path':row['frozen'],'sha256':row['sha256'],'bytes':row['bytes']})
  p=ROOT/row['live'];now=sha(p.read_bytes()) if p.exists() else None
  if now!=row['sha256']:drift.append({'path':row['live'],'frozen_sha256':row['sha256'],'live_sha256':now,'classification':'live shared-input drift, separate from frozen integrity'})
 for row in read(S/'dependency-manifest.json'):check(row)
 cm=read(ROOT/'frontier/sources/i14_spectral_width_novelty_r3/corpus-manifest.json')
 tree=read(S/'inputs/sources/preprints-tree.json')
 lookup={r['path']:r for r in tree['tree']}
 require(cm['pin']==PIN,'corpus pin')
 require(not tree['truncated'],'truncated tree')
 require(sum(r['type']=='tree' and r['path'].count('/')==1 for r in tree['tree'])==749,'749 inventory')
 require(len(cm['files'])==9340,'9340 corpus')
 for row in cm['files']:
  p=CORPUS/row['path'];b=p.read_bytes()
  require(sha(b)==row['sha256'],'corpus SHA '+row['path'])
  require(blob(b)==row['git_blob'],'corpus Git '+row['path'])
  require(lookup[row['path']]['sha']==row['git_blob'],'tree Git '+row['path'])
  url=urllib.parse.unquote(row['url'])
  require(url=='https://raw.githubusercontent.com/openai/math/'+PIN+'/'+row['path'],'pinned URL '+row['path'])
 selected=read(S/'source-manifest.json')
 for row in selected:
  b=(CORPUS/row['path']).read_bytes()
  require(sha(b)==row['sha256'] and blob(b)==row['git_blob'],'selected source '+row['path'])
 passages=read(S/'read-passages.json')
 for row in passages:
  lines=(ROOT/row['path']).read_bytes().splitlines(keepends=True)
  require(1<=row['start_line']<=row['end_line']<=len(lines),'passage range '+row['path'])
  b=b''.join(lines[row['start_line']-1:row['end_line']])
  require(sha(b)==row['sha256'],'passage hash '+row['path'])
 contracts=read(S/'contracts.json')
 for row in contracts:check(row)
 primary=[]
 for manifest in sorted((S/'literature').glob('manifest*.json')):
  for row in read(manifest):
   check(row)
   if 'extraction' in row:
    check(row['extraction']);require((ROOT/row['path']).read_bytes().startswith(b'%PDF'),'non-PDF extracted '+row['path'])
   primary.append(row)
 challenge=S/'literature/bk-published.pdf'
 require(not challenge.read_bytes().startswith(b'%PDF'),'documented challenge became PDF')
 require(any(r['status']==403 and r['path'].endswith('dnwp-published.pdf') for r in primary),'documented 403 missing')
 diag=read(E/'diagnostics.json')
 require(diag['summary']['closed_form']==45 and diag['summary']['dag']==128 and diag['summary']['facets']==90 and diag['summary']['transports']==18,'diagnostic counts')
 for row in diag['closed_form_cases']:
  a,k=F(row['a']),F(row['kappa'])
  require(F(row['moment_ratio'])==a+k*k/(9*a),'closed moment identity')
  require(F(row['potential_speed_ratio_squared'])==((1-a)*k*k/9+a/3)/a,'potential speed identity')
 for row in diag['transport_cases']:
  err,cost=F(row['squared_map_error']),F(row['W2_squared'])
  require(0<cost<=err,'optimal cost vs graph cost')
  require(F(row['D6_over_W2_squared'])==err**3/cost,'map exponent diagnostic')
 require(any(row['zero_cells']>0 for row in diag['transport_cases']),'zero-cell exercise')
 numeric=read(E/'fixed-mass-search.json')
 require(len(numeric['cases'])==15,'floating cases')
 require(numeric['summary']['max_residual']<1e-11,'floating mass residual')
 require(numeric['summary']['max_grid_difference']<1e-6,'floating refinement difference')
 report=REPORT.read_text()
 require(not any(ord(c)<32 and c not in '\n\t' for c in report),'report control characters')
 require(report.count('$$')%2==0,'display-math delimiters')
 (E/'live-drift.json').write_text(json.dumps(drift,indent=2)+'\n')
 result={'status':'PASS' if not errors else 'FAIL','scope':'integrity and finite diagnostics only; no analytic proof/significance certification','sealed_artifacts':len(seal['files']),'frozen_inputs':len(inputs),'selected_sources':len(selected),'corpus_files':len(cm['files']),'manuscripts':749,'contracts':len(contracts),'read_passages':len(passages),'primary_responses':len(primary),'primary_extractions':sum('extraction' in r for r in primary),'documented_nonpaper_or_failed_responses':2,'diagnostics':diag['summary'],'floating_diagnostics':numeric['summary'],'live_shared_drift':drift,'errors':errors}
 (E/'verification.json').write_text(json.dumps(result,indent=2)+'\n')
 print(json.dumps(result,indent=2))
 if errors:raise SystemExit(1)

if __name__=='__main__':main()
